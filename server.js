const express = require('express');
const fs = require('fs');
const path = require('path');

const app = express();
const PORT = process.env.PORT || 3000;
const STATE_FILE = path.join(__dirname, 'state.json');

app.use(express.text({ type: '*/*' }));
app.use(express.static(path.join(__dirname, 'public')));

// =================== 設定（SmartBinUI と同じ） ===================
const CFG = {
  COLLECT_DAYS: [1, 4],        // 月=1, 火=2, 水=3, 木=4, 金=5, 土=6, 日=7
  DEADLINE_H: 8,
  DEADLINE_M: 30,
  BAG_LITERS: 20,              // 20L袋
  YEN_PER_LITER: 2,            // 1Lあたり2円（20L=40円）
  BAG_GRAMS: 14.0,             // 袋1枚の重さ [g]
  CO2_PER_G_PE: 3.14,          // PE 1g 焼却時の CO2 [g]
  CEDAR_KG_PER_YEAR: 8.8,      // スギ1本の年間CO2吸収量 [kg]
  SAPPORO_HOUSEHOLDS: 1005912, // 札幌市の世帯数
  MAX_HOLD_DAYS: 8,            // 衛生上の最長保管日数
  MIN_FILL_TO_COUNT: 5         // ごみなしとみなす閾値 [%]
};

const MIN_MS = 60000;
const HOUR_MS = 3600000;
const DAY_MS = 86400000;
const JST_OFFSET = 9 * HOUR_MS;

const D_COLLECTING = 0;
const D_EMPTY      = 1;
const D_SKIP       = 2;
const D_TAKE       = 3;
const D_FULL       = 4;
const D_OVERFLOW   = 5;

const WD = ['月', '火', '水', '木', '金', '土', '日'];

// ================= 日本時間（JST）ヘルパー =================
function jstDate(ms) {
  return new Date(ms + JST_OFFSET);
}
function getDow1to7(ms) {
  const d = jstDate(ms).getUTCDay(); // 0(日)〜6(土)
  return d === 0 ? 7 : d;
}
function dayKey(ms) {
  const d = jstDate(ms);
  return Math.floor(Date.UTC(d.getUTCFullYear(), d.getUTCMonth(), d.getUTCDate()) / DAY_MS);
}
function md(ms) {
  const d = jstDate(ms);
  return `${d.getUTCMonth() + 1}/${d.getUTCDate()}（${WD[getDow1to7(ms) - 1]}）`;
}
function hm(ms) {
  const d = jstDate(ms);
  return `${d.getUTCHours()}:${String(d.getUTCMinutes()).padStart(2, '0')}`;
}
function dayWord(ms, now) {
  const diff = dayKey(ms) - dayKey(now);
  if (diff === 0) return '今日';
  if (diff === 1) return '明日';
  if (diff > 1 && diff < 7) return `${WD[getDow1to7(ms) - 1]}曜`;
  return md(ms);
}
function whenText(ms, now) {
  if (ms - now > 14 * DAY_MS) return '2週間以上先';
  const dw = dayWord(ms, now);
  const w = (dw === '今日' || dw === '明日') ? `${dw} ` : md(ms);
  return `${w}${jstDate(ms).getUTCHours()}時ごろ`;
}
function isCollectDay(dow) {
  return CFG.COLLECT_DAYS.includes(dow);
}
function nextDeadline(after) {
  const d = jstDate(after);
  for (let i = 0; i < 15; i++) {
    const candidate = new Date(Date.UTC(d.getUTCFullYear(), d.getUTCMonth(), d.getUTCDate() + i, CFG.DEADLINE_H, CFG.DEADLINE_M, 0, 0));
    const ms = candidate.getTime() - JST_OFFSET;
    const dow = getDow1to7(ms);
    if (isCollectDay(dow) && ms > after) return ms;
  }
  return after + 7 * DAY_MS;
}

// ================= Model クラス（Model.pde の移植） =================
class Model {
  constructor(start) {
    this.emptyMm = 300;
    this.fullMm = 50;
    this.fill = 0;
    this.dA = -1;
    this.dB = -1;
    this.dHand = -1;
    this.lid = 0;
    this.hello = false;
    this.lastRxRealMs = -100000;
    this.errCode = 0;
    this.errRealMs = -100000;

    this.hist = [{ t: start, f: 0 }];
    this.log = [];
    this.toasts = [];
    this.toastSeq = 0;

    this.startMs = start;
    this.bagStart = start;
    this.lastDeadline = start;
    this.bagOutSinceDeadline = false;
    this.savedBags = 0;
    this.usedBags = 0;
    this.outFillSum = 0;
    this.prevBagRate = -1;
    this.lastThrowT = -1;
    this.lastThrowPct = 0;

    this.rate = -1;
    this.rateSrc = '';
    this.d1 = nextDeadline(start);
    this.d2 = nextDeadline(this.d1);
    this.fillAtD1 = -1;
    this.fillAtD2 = -1;
    this.tFull = -1;
    this.decision = D_COLLECTING;
    this.headline = '';
    this.sub = '';
  }

  pushToast(text) {
    this.toastSeq++;
    this.toasts.push({ id: this.toastSeq, text, at: Date.now() });
    if (this.toasts.length > 5) this.toasts.shift();
  }

  evToast(text) {
    if (demo && sim && (sim.preloading || timeScale > 60)) return;
    this.pushToast(text);
  }

  handleLine(line, t) {
    if (!line) return;
    line = line.trim();
    if (!line) return;
    const p = line.split(',');
    this.lastRxRealMs = Date.now();
    const k = p[0];

    if (k === 'H' && p.length >= 5) {
      this.emptyMm = parseInt(p[3], 10) || 300;
      this.fullMm = parseInt(p[4], 10) || 50;
      if (this.emptyMm <= this.fullMm) { this.emptyMm = 300; this.fullMm = 50; }
      this.hello = true;
    } else if (k === 'S' && p.length >= 7) {
      this.lid = parseInt(p[2], 10) || 0;
      this.dHand = parseInt(p[3], 10);
      this.dA = parseInt(p[4], 10);
      this.dB = parseInt(p[5], 10);
      const f = Math.min(100, Math.max(0, parseInt(p[6], 10) || 0));
      this.setFill(f, t);
    } else if (k === 'E' && p.length >= 3) {
      this.onEvent(p, t);
    }
  }

  setFill(f, t) {
    if (this.fill >= 25 && f <= CFG.MIN_FILL_TO_COUNT && this.lid === 0) {
      this.onBagOut(t, this.fill);
      if (!demo) commandQueue.push('C,RESET');
      this.evToast('袋の交換を検知しました');
    }
    this.fill = f;
    this.addSample(t, f);
  }

  onEvent(p, t) {
    const kind = p[2];
    const v1 = p.length > 3 ? (parseInt(p[3], 10) || 0) : 0;
    const v2 = p.length > 4 ? (parseInt(p[4], 10) || 0) : 0;
    if (kind === 'THROW') {
      const d = ((v1 - v2) * 100.0) / Math.max(1, this.emptyMm - this.fullMm);
      this.lastThrowT = t;
      this.lastThrowPct = d;
      this.addLog(t, `投入 +${Math.round(d)}%`);
      this.evToast(`ごみを検知しました  +${Math.round(d)}%`);
    } else if (kind === 'FULL') {
      this.addLog(t, '満杯');
      this.evToast('満杯になりました');
    } else if (kind === 'ERR') {
      this.errCode = v1;
      this.errRealMs = Date.now();
      const errMap = {
        1: '内側センサ A が測れていません',
        2: '内側センサ B が測れていません',
        3: '外側センサ（手の検知）が測れていません'
      };
      this.evToast(errMap[v1] || `センサの異常（${v1}）`);
    }
  }

  onBagOut(t, f) {
    if (f >= CFG.MIN_FILL_TO_COUNT) {
      this.usedBags++;
      this.outFillSum += f;
      const hrs = (t - this.bagStart) / HOUR_MS;
      if (hrs > 12 && f > 20) this.prevBagRate = f / hrs;
      this.addLog(t, `袋を出した（使用率 ${Math.round(f)}%）`);
    }
    this.bagStart = t;
    this.bagOutSinceDeadline = true;
    this.fill = 0;
    this.addSample(t, 0);
  }

  addSample(t, f) {
    const last = this.hist[this.hist.length - 1];
    if (t < last.t) t = last.t;
    if (Math.abs(f - last.f) >= 1 || t - last.t >= 30 * MIN_MS) {
      this.hist.push({ t, f });
    }
    while (this.hist.length > 1 && this.hist[0].t < t - 15 * DAY_MS) {
      this.hist.shift();
    }
  }

  addLog(t, text) {
    this.log.push({ t, text });
    if (this.log.length > 200) this.log.shift();
  }

  update(t) {
    let nd = nextDeadline(this.lastDeadline);
    while (nd <= t) {
      if (!this.bagOutSinceDeadline && this.fillAt(nd) >= CFG.MIN_FILL_TO_COUNT) {
        this.savedBags++;
        this.addLog(nd, '収集日を見送り → 袋1枚節約');
      }
      this.bagOutSinceDeadline = false;
      this.lastDeadline = nd;
      nd = nextDeadline(nd);
    }

    const ws = Math.max(this.bagStart, t - 72 * HOUR_MS);
    const spanH = (t - ws) / HOUR_MS;
    const f0 = (ws === this.bagStart) ? 0 : this.fillAt(ws);
    const cur = spanH > 0 ? (this.fill - f0) / spanH : 0;

    this.rate = -1;
    this.rateSrc = '';
    if (spanH >= 24) {
      this.rate = Math.max(cur, 0.05);
      this.rateSrc = `直近 ${Math.round(spanH)} 時間のたまり方`;
    } else if (this.prevBagRate > 0) {
      const w = spanH / 24.0;
      this.rate = w * Math.max(cur, 0) + (1 - w) * this.prevBagRate;
      this.rateSrc = `いまの袋 ${Math.round(w * 100)}% ＋ 前の袋 ${Math.round((1 - w) * 100)}% のペース`;
    } else if (spanH >= 6 && cur > 0) {
      this.rate = cur;
      this.rateSrc = `直近 ${Math.round(spanH)} 時間のたまり方`;
    }
    if (this.rate > 0) this.rate = Math.max(this.rate, 0.05);

    this.d1 = nextDeadline(t);
    this.d2 = nextDeadline(this.d1);
    if (this.rate > 0) {
      this.fillAtD1 = this.fill + (this.rate * (this.d1 - t)) / HOUR_MS;
      this.fillAtD2 = this.fill + (this.rate * (this.d2 - t)) / HOUR_MS;
      this.tFull = this.fill >= 100 ? t : t + ((100 - this.fill) / this.rate) * HOUR_MS;
    } else {
      this.fillAtD1 = -1;
      this.fillAtD2 = -1;
      this.tFull = -1;
    }
    this.decide(t);
  }

  decide(t) {
    const holdD2 = (this.d2 - this.bagStart) / DAY_MS;
    const w1 = dayWord(this.d1, t);
    const w2 = dayWord(this.d2, t);
    const today = w1 === '今日';
    const takeLine = today ? `今日 ${hm(this.d1)} までに出しましょう` : `${w1}の朝に出しましょう`;

    if (this.fill >= 90) {
      this.decision = D_FULL;
      this.headline = takeLine;
      this.sub = `ほぼ満杯です（${Math.round(this.fill)}%）。${today ? '' : 'それまでは押し込みすぎないように。'}`;
    } else if (this.fill < CFG.MIN_FILL_TO_COUNT) {
      this.decision = D_EMPTY;
      this.headline = 'まだ空っぽです';
      this.sub = 'ごみを入れるたびに、出す日を予測し直します。';
    } else if (this.rate <= 0) {
      this.decision = D_COLLECTING;
      this.headline = 'たまるペースを学習中';
      this.sub = 'あと何回かごみを入れると、出す日を予測できます。';
    } else if (this.fillAtD1 >= 100) {
      this.decision = D_OVERFLOW;
      this.headline = `${w1}より前に満杯になりそう`;
      this.sub = `満杯予測は ${whenText(this.tFull, t)}。ごみをならすか、小さくしてから捨てましょう。`;
    } else if (this.fillAtD2 >= 100 || holdD2 > CFG.MAX_HOLD_DAYS) {
      this.decision = D_TAKE;
      this.headline = takeLine;
      if (this.fillAtD2 < 100) {
        this.sub = `${w2}まで待つと ${Math.round(holdD2)} 日ためることになるため（衛生のため ${Math.round(CFG.MAX_HOLD_DAYS)} 日まで）。`;
      } else {
        this.sub = `${w2}まで待つと、あふれる見込みです（約 ${Math.round(Math.min(this.fillAtD2, 199))}%）。`;
      }
    } else {
      this.decision = D_SKIP;
      this.headline = today ? '今日は出さなくてOK' : `${w1}は見送りでOK`;
      const ni = (today || w1 === '明日') ? '' : 'に';
      this.sub = `${w2}まで待てば、袋を約 ${Math.round(this.fillAtD2)}% まで使えます（${w1}${ni}出すと ${Math.round(this.fillAtD1)}%）。`;
    }
  }

  isAction() {
    return this.decision === D_TAKE || this.decision === D_FULL || this.decision === D_OVERFLOW;
  }

  targetPickup() {
    if (this.decision === D_SKIP) return this.d2;
    if (this.isAction()) return this.d1;
    return -1;
  }

  fillAt(t) {
    if (t < this.hist[0].t) return this.hist[0].f;
    let lo = 0, hi = this.hist.length - 1;
    while (lo < hi) {
      const mid = (lo + hi + 1) >> 1;
      if (this.hist[mid].t <= t) lo = mid;
      else hi = mid - 1;
    }
    return this.hist[lo].f;
  }

  pctOf(d) {
    if (d < 0) return -1;
    return Math.min(100, Math.max(0, ((this.emptyMm - d) * 100.0) / Math.max(1, this.emptyMm - this.fullMm)));
  }

  saveState() {
    const obj = {
      startMs: this.startMs,
      bagStart: this.bagStart,
      savedBags: this.savedBags,
      usedBags: this.usedBags,
      outFillSum: this.outFillSum,
      prevBagRate: this.prevBagRate,
      hist: this.hist
    };
    try { fs.writeFileSync(STATE_FILE, JSON.stringify(obj)); } catch (e) {}
  }

  loadState() {
    if (!fs.existsSync(STATE_FILE)) return;
    try {
      const j = JSON.parse(fs.readFileSync(STATE_FILE, 'utf8'));
      this.startMs = j.startMs || this.startMs;
      this.bagStart = j.bagStart || this.bagStart;
      this.savedBags = j.savedBags || 0;
      this.usedBags = j.usedBags || 0;
      this.outFillSum = j.outFillSum || 0;
      this.prevBagRate = j.prevBagRate ?? -1;
      if (Array.isArray(j.hist) && j.hist.length > 0) {
        this.hist = j.hist;
        this.fill = this.hist[this.hist.length - 1].f;
      }
      this.lastDeadline = Date.now();
    } catch (e) {}
  }
}

// ================= Sim クラス（Sim.pde の移植） =================
class Sim {
  constructor(start, m) {
    this.t = start;
    this.m = m;
    this.f = 0;
    this.skew = 0;
    this.lidUntilRealMs = 0;
    this.preloading = false;
  }

  advanceTo(target) {
    this.preloading = (target - this.t) > 2 * DAY_MS;
    let steps = 0;
    while (this.t + MIN_MS <= target && steps < 400000) {
      this.t += MIN_MS;
      this.minute(this.t);
      this.m.update(this.t);
      steps++;
    }
    this.preloading = false;
  }

  minute(tt) {
    const d = jstDate(tt);
    const h = d.getUTCHours();
    const min = d.getUTCMinutes();

    let p = 0.0012;
    if      (h >= 18 && h < 23) p = 0.007;
    else if (h >= 7  && h < 9)  p = 0.004;
    else if (h >= 11 && h < 14) p = 0.002;
    else if (h >= 1  && h < 6)  p = 0.0001;

    if (Math.random() < p) {
      this.throwSome(tt, 2 + Math.random() * 3.5);
    }

    if (h === 7 && min === 40 && dayWord(this.m.d1, tt) === '今日' && this.m.isAction()) {
      this.takeOut(tt);
    }

    this.skew = Math.min(22, Math.max(-22, this.skew + (Math.random() * 2.4 - 1.2)));
    this.emitS(tt);
  }

  distOf(pct) {
    return Math.round(this.m.emptyMm - (pct / 100.0) * (this.m.emptyMm - this.m.fullMm));
  }

  throwSome(tt, pct) {
    if (this.f >= 100) return;
    const before = this.f;
    this.f = Math.min(100, this.f + pct);
    const now = Date.now();
    this.m.handleLine(`E,${now},LID_OPEN,0,0`, tt);
    this.m.handleLine(`E,${now},THROW,${this.distOf(before)},${this.distOf(this.f)}`, tt);
    this.m.handleLine(`E,${now},LID_CLOSE,0,0`, tt);
    if (this.f >= 100) this.m.handleLine(`E,${now},FULL,100,0`, tt);
  }

  emitS(tt) {
    const base = this.distOf(this.f);
    const a = base - Math.round(this.skew);
    const b = base + Math.round(this.skew);
    const lidState = Date.now() < this.lidUntilRealMs ? 2 : 0;
    this.m.handleLine(`S,${Date.now()},${lidState},-1,${a},${b},${Math.round(this.f)}`, tt);
  }

  manualThrow(tt) {
    this.lidUntilRealMs = Date.now() + 1500;
    this.throwSome(tt, 3 + Math.random() * 4);
    this.emitS(tt);
  }

  takeOut(tt) {
    this.m.onBagOut(tt, this.m.fill);
    this.f = 0;
    this.skew = 0;
    this.emitS(tt);
  }

  lidPulse() {
    this.lidUntilRealMs = Date.now() + 2000;
  }
}

// ================= アプリケーション状態とループ =================
let demo = false;
let autoLid = true;
let timeScale = 1;
let vNow = Date.now();
let lastTickRealMs = Date.now();
let lastSaveRealMs = Date.now();
let commandQueue = [];

let model = new Model(vNow);
model.loadState();
let sim = null;

function startDemo() {
  if (!demo && model) model.saveState();
  demo = true;
  timeScale = 1;
  vNow = Date.now();
  const start = vNow - 21 * DAY_MS;
  model = new Model(start);
  sim = new Sim(start, model);
  model.handleLine('H,TRASHCAN,1.1,300,50', start);
  sim.advanceTo(vNow); // 3週間分を一気に早送り生成
  model.pushToast('デモモード：3週間分のデータを生成しました');
}

function startLive() {
  demo = false;
  timeScale = 1;
  vNow = Date.now();
  model = new Model(vNow);
  model.loadState();
  sim = null;
  commandQueue.push('C,PING');
  model.pushToast('実機モードに切り替えました');
}

// サーバー側ティック（250msごとに仮想時計とモデルを更新）
setInterval(() => {
  const nowReal = Date.now();
  const dt = nowReal - lastTickRealMs;
  lastTickRealMs = nowReal;

  if (demo && sim) {
    vNow += dt * timeScale;
    sim.advanceTo(vNow);
    model.lid = nowReal < sim.lidUntilRealMs ? 2 : 0;
  } else {
    vNow = nowReal;
    if (nowReal - lastSaveRealMs > 60000) {
      model.saveState();
      lastSaveRealMs = nowReal;
    }
  }
  model.update(vNow);
}, 250);

// ================= HTTP エンドポイント =================
// 1. Arduino Uno R4 WiFi からの受信
app.post('/api/line', (req, res) => {
  const line = (req.body || '').trim();
  if (!demo && line) {
    model.handleLine(line, Date.now());
  }
  const nextCmd = (!demo && commandQueue.length > 0) ? commandQueue.shift() : 'OK';
  res.send(nextCmd);
});

// 2. Webブラウザからの操作（キー操作 / ボタン操作）
app.post('/api/action', (req, res) => {
  let payload = {};
  try { payload = JSON.parse(req.body); } catch (e) {}
  const { act, val } = payload;

  if (act === 'THROW') {
    if (demo && sim) sim.manualThrow(vNow);
    else commandQueue.push('C,THROW');
  } else if (act === 'RESET') {
    if (demo && sim) sim.takeOut(vNow);
    else {
      commandQueue.push('C,RESET');
      model.onBagOut(vNow, model.fill);
      model.saveState();
    }
    model.pushToast('袋を出しました。記録を区切ります');
  } else if (act === 'OPEN') {
    if (demo && sim) sim.lidPulse();
    else commandQueue.push('C,OPEN');
  } else if (act === 'CLOSE') {
    if (!demo) commandQueue.push('C,CLOSE');
  } else if (act === 'CAL_EMPTY' && !demo) {
    commandQueue.push('C,CAL,EMPTY');
    model.pushToast('いまの距離を「空」の基準にしました');
  } else if (act === 'CAL_FULL' && !demo) {
    commandQueue.push('C,CAL,FULL');
    model.pushToast('いまの距離を「満杯」の基準にしました');
  } else if (act === 'AUTO' && !demo) {
    autoLid = !autoLid;
    commandQueue.push(`C,AUTO,${autoLid ? 1 : 0}`);
    model.pushToast(autoLid ? '自動開閉 ON' : '自動開閉 OFF');
  } else if (act === 'SPEED') {
    if (!demo) {
      model.pushToast('実機モードでは時間を早送りできません');
    } else {
      const sc = [1, 60, 3600, 86400];
      const nm = ['実時間', '1秒 = 1分', '1秒 = 1時間', '1秒 = 1日'];
      const idx = Math.min(3, Math.max(0, Number(val) || 0));
      timeScale = sc[idx];
      model.pushToast(`時間の速さ：${nm[idx]}`);
    }
  } else if (act === 'TOGGLE_MODE') {
    if (demo) startLive();
    else startDemo();
  }

  res.json({ ok: true });
});

// 3. 画面描画用の全データ配信
app.get('/api/
