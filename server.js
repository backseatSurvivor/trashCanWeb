const express = require('express');
const fs = require('fs');
const path = require('path');

const app = express();
const PORT = process.env.PORT || 3000;
const LOG_FILE = path.join(__dirname, 'trash_log.json');

app.use(express.text({ type: '*/*' })); // Arduinoからの生テキストを受け取る
app.use(express.static(path.join(__dirname, 'public')));

// ================= 設定（trash_dashboard.pde と同じ） =================
const CONFIG = {
  COLLECTION_DOW: [1, 4], // 0:日, 1:月, 2:火, 3:水, 4:木, 5:金, 6:土
  COLLECTION_HOUR: 8,
  COLLECTION_MIN: 30,
  BAG_YEN: 80,
  FULL_LINE: 90,
  UNEVEN_MM: 60,
  RATE_WINDOW_MS: 7 * 24 * 3600 * 1000,
  MIN_SPAN_MS: 12 * 3600 * 1000
};

// ================= 状態管理 =================
let state = {
  curPct: 0,
  lidState: 0,
  handMM: -1,
  fillAMM: -1,
  fillBMM: -1,
  emptyMM: 300,
  fullMM: 50,
  lastRx: 0,
  deviceVersion: '-'
};

let history = [];
let logs = [];
let commandQueue = []; // Arduinoへ送るコマンド待ち行列

// 起動時にログ復元
if (fs.existsSync(LOG_FILE)) {
  try {
    history = JSON.parse(fs.readFileSync(LOG_FILE, 'utf8'));
    if (history.length > 0) state.curPct = history[history.length - 1].pct;
  } catch (e) { history = []; }
}
if (history.length === 0) addRec('START', 0, 0);

function addLog(msg) {
  const d = new Date(Date.now() + 9 * 3600 * 1000); // JST
  const ts = `${d.getUTCMonth() + 1}/${d.getUTCDate()} ${String(d.getUTCHours()).padStart(2, '0')}:${String(d.getUTCMinutes()).padStart(2, '0')}`;
  logs.push(`${ts}  ${msg}`);
  if (logs.length > 60) logs.shift();
}

function addRec(type, pct, delta) {
  history.push({ t: Date.now(), type, pct, delta });
  try { fs.writeFileSync(LOG_FILE, JSON.stringify(history)); } catch (e) {}
}

// ================= 収集日・判定ロジック =================
function nextCollection(tMs) {
  // 日本時間(UTC+9)基準で計算
  const jstOffset = 9 * 3600 * 1000;
  const d = new Date(tMs + jstOffset);
  d.setUTCHours(CONFIG.COLLECTION_HOUR, CONFIG.COLLECTION_MIN, 0, 0);

  for (let i = 0; i < 15; i++) {
    const dow = d.getUTCDay();
    const candidateMs = d.getTime() - jstOffset;
    if (CONFIG.COLLECTION_DOW.includes(dow) && candidateMs > tMs) {
      return candidateMs;
    }
    d.setUTCDate(d.getUTCDate() + 1);
  }
  return tMs + 7 * 24 * 3600 * 1000;
}

function computeStatsAndDecision(now) {
  // 袋の枚数とロスの再計算
  let smartBags = 0, smartWaste = 0;
  let naiveBags = 0, naiveWaste = 0, naivePct = 0;

  const naiveThrow = (d) => {
    naivePct += d;
    while (naivePct >= 100) { naiveBags++; naivePct -= 100; }
  };
  const naiveCollect = () => {
    if (naivePct > 0.5) {
      naiveBags++;
      naiveWaste += ((100 - naivePct) / 100) * CONFIG.BAG_YEN;
      naivePct = 0;
    }
  };

  let c = nextCollection(history[0].t);
  for (const r of history) {
    while (c <= r.t) { naiveCollect(); c = nextCollection(c); }
    if (r.type === 'THROW') naiveThrow(r.delta);
    if (r.type === 'RESET') {
      smartBags++;
      smartWaste += ((100 + r.delta) / 100) * CONFIG.BAG_YEN;
    }
  }
  while (c <= now) { naiveCollect(); c = nextCollection(c); }

  // 判定ロジック
  const c1 = nextCollection(now);
  const c2 = nextCollection(c1);
  const from = now - CONFIG.RATE_WINDOW_MS;
  let first = -1, sum = 0;

  for (const r of history) {
    if (r.t > now) break;
    if (first < 0) first = r.t;
    if (r.t >= from && r.type === 'THROW') sum += r.delta;
  }

  let dec = { verdict: 0, ratePerDay: 0, fullAt: 0, c1, c2, pctAtC1: 0, lossYen: 0 };
  if (first >= 0) {
    const span = now - Math.max(from, first);
    if (span >= CONFIG.MIN_SPAN_MS && sum > 0) {
      const perMs = sum / span;
      dec.ratePerDay = perMs * 24 * 3600 * 1000;
      dec.fullAt = state.curPct >= CONFIG.FULL_LINE ? now : now + (CONFIG.FULL_LINE - state.curPct) / perMs;
      dec.pctAtC1 = Math.min(100, state.curPct + perMs * (c1 - now));
      dec.lossYen = ((100 - dec.pctAtC1) / 100) * CONFIG.BAG_YEN;

      if (dec.fullAt <= c1) dec.verdict = 3;
      else if (dec.fullAt <= c2) dec.verdict = 2;
      else dec.verdict = 1;
    }
  }

  return { smartBags, smartWaste, naiveBags, naiveWaste, dec };
}

// ================= APIエンドポイント =================
// 1. Arduinoからの受信口（1行ずつ送られてくる）
app.post('/api/line', (req, res) => {
  const line = (req.body || '').trim();
  if (line) {
    state.lastRx = Date.now();
    const f = line.split(',');
    const k = line.charAt(0);

    if (k === 'H' && f.length >= 5) {
      state.deviceVersion = f[2];
      state.emptyMM = parseInt(f[3], 10) || 300;
      state.fullMM = parseInt(f[4], 10) || 50;
      addLog(`Arduino接続 v${f[2]}`);
    } else if (k === 'S' && f.length >= 7) {
      state.lidState = parseInt(f[2], 10);
      state.handMM = parseInt(f[3], 10);
      state.fillAMM = parseInt(f[4], 10);
      state.fillBMM = parseInt(f[5], 10);
      state.curPct = parseInt(f[6], 10);
    } else if (k === 'E' && f.length >= 5) {
      const type = f[2];
      const v1 = parseInt(f[3], 10);
      const v2 = parseInt(f[4], 10);
      if (type === 'THROW') {
        const spanMM = Math.max(1, state.emptyMM - state.fullMM);
        const d = ((v1 - v2) * 100.0) / spanMM;
        const after = Math.min(100, Math.max(0, ((state.emptyMM - v2) * 100.0) / spanMM));
        if (d > 0) {
          state.curPct = after;
          addRec('THROW', after, d);
          addLog(`投入 +${d.toFixed(1)}%`);
        }
      } else if (type === 'FULL') {
        addLog('満杯ライン到達');
      } else if (type === 'ERR') {
        addLog(`センサ異常 code=${v1}`);
      }
    }
  }

  // キューにコマンドがあればレスポンスとして返す
  const nextCmd = commandQueue.length > 0 ? commandQueue.shift() : 'OK';
  res.send(nextCmd);
});

// 2. Webブラウザからのコマンド送信（OPEN / CLOSE / THROW / RESET）
app.post('/api/cmd', (req, res) => {
  const cmd = (req.body || '').trim();
  if (cmd === 'C,RESET') {
    addLog(`ごみ袋を交換（${Math.round(state.curPct)}%）`);
    addRec('RESET', 0, -state.curPct);
    state.curPct = 0;
  } else if (cmd === 'SIM_THROW') {
    // テスト用：サーバー単体で疑似投入するボタン用
    const d = 5 + Math.random() * 6;
    state.curPct = Math.min(100, state.curPct + d);
    addRec('THROW', state.curPct, d);
    addLog(`テスト投入 +${d.toFixed(1)}%`);
    return res.json({ ok: true });
  }
  commandQueue.push(cmd);
  addLog(`コマンド予約: ${cmd}`);
  res.json({ ok: true });
});

// 3. Webダッシュボード用データ取得
app.get('/api/status', (req, res) => {
  const now = Date.now();
  const { smartBags, smartWaste, naiveBags, naiveWaste, dec } = computeStatsAndDecision(now);
  const weekAgo = now - CONFIG.RATE_WINDOW_MS;
  res.json({
    now,
    config: CONFIG,
    state,
    dec,
    stats: { smartBags, smartWaste, naiveBags, naiveWaste },
    history: history.filter(r => r.t >= weekAgo),
    logs: logs.slice(-8)
  });
});

app.listen(PORT, () => console.log(`Server running on port ${PORT}`));