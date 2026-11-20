const express = require('express');
const fs = require('fs');
const path = require('path');

const app = express();
const PORT = process.env.PORT || 3000;
const STATE_FILE = path.join(__dirname, 'state.json');

app.use(express.text({ type: '*/*' }));
app.use(express.static(path.join(__dirname, 'public')));

// =================== 設定 ===================
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
  MIN_FILL_TO_COUNT: 5,        // ごみなし（ほぼゼロ）とみなす閾値 [%]
  BAG_OUT_CONFIRM_COUNT: 2     // 袋出し自動検知に必要な連続回数（約3秒）
};

const MIN_MS = 60000;
const HOUR_MS = 3600000;
const DAY_MS = 86400000;
const JST_OFFSET = 9 * HOUR_MS;
const CMD_TTL_MS = 10000;

const D_COLLECTING = 0;
const D_EMPTY      = 1;
const D_SKIP       = 2;
const D_TAKE       = 3;
const D_FULL       = 4;
const D_OVERFLOW   = 5;

const WD = ['月', '火', '水', '木', '金', '土', '日'];

const SPEED_SCALES = [1, 60, 3600, 21600, 86400];
const SPEED_NAMES  = [
  '実時間 (×1)',
  '1秒 = 1分 (×60)',
  '1秒 = 1時間 (×3600)',
  '1秒 = 6時間 (×21600)',
  '1秒 = 1日 (×86400)'
];

// ================= グローバル状態（必ずクラス定義より先に宣言） =================
let autoLid = true;
let timeScale = 1;
let vNow = Date.now();
let lastTickRealMs = Date.now();
let lastSaveRealMs = Date.now();
let simLidUntilRealMs = 0;
let commandQueue = [];
let demoSkew = 0;
let nextDemoThrowRealMs = Date.now() + 5000;
let nextDemoThrowVMs = vNow + 4 * HOUR_MS;

// ================= 日本時間（JST）ヘルパー =================
function jstDate(ms) { return new Date(ms + JST_OFFSET); }
function getDow1to7(ms) {
  const d = jstDate(ms).getUTCDay();
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

// ================= Model クラス =================
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
    this.deviceKind = 'none'; // 'none' | 'real' | 'demo'
    this.lastRxRealMs = -100000;
    this.errCode = 0;
    this.errRealMs = -100000;
    this.ignoreStaleUntilRealMs = 0;
    this.lowFillStreak = 0;

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
    this.decision = D_EMPTY;
    this.headline = 'まだ空っぽです';
    this.sub = 'ごみを入れるたびに、出す日を予測し直します。';
  }

  pushToast(text) {
    this.toastSeq++;
    this.toasts.push({ id: this.toastSeq, text, at: Date.now() });
    if (this.toasts.length > 5) this.toasts.shift();
  }

  evToast(text) {
    if (timeScale > 60) return;
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
      const modeTag = (p.length >= 6 ? p[5] : '').trim().toUpperCase();
      this.deviceKind = (modeTag === 'DEMO') ? 'demo' : 'real';
      this.lowFillStreak = 0;
      if (this.deviceKind === 'demo') {
        syncDemoDeviceIfNeeded();
      }
    } else if (k === 'S' && p.length >= 7) {
      if (!this.hello) {
        enqueueCommand('C,PING');
        return;
      }

      const repLid = parseInt(p[2], 10) || 0;
      const repDA = parseInt(p[4], 10);
      const repDB = parseInt(p[5], 10);
      const f = Math.min(100, Math.max(0, parseInt(p[6], 10) || 0));

      if (this.deviceKind === 'demo') {
        const curDA = this.dA >= 0 ? Math.round(this.dA) : this.emptyMm;
        const curDB = this.dB >= 0 ? Math.round(this.dB) : this.emptyMm;
        if (f !== Math.round(this.fill) || repLid !== this.lid || repDA !== curDA || repDB !== curDB) {
          syncDemoDeviceIfNeeded();
        }
        return;
      }

      this.lid = repLid;
      this.dHand = parseInt(p[3], 10);

      if (Date.now() < this.ignoreStaleUntilRealMs && f > CFG.MIN_FILL_TO_COUNT) {
        return;
      }
      if (f <= CFG.MIN_FILL_TO_COUNT) {
        this.ignoreStaleUntilRealMs = 0;
      }

      const fillStatus = this.setFill(f, t, true);
      if (fillStatus === 'updated') {
        this.dA = repDA;
        this.dB = repDB;
      }
    } else if (k === 'E' && p.length >= 3) {
      if (!this.hello) {
        enqueueCommand('C,PING');
        return;
      }
      if (this.deviceKind === 'demo') return;
      if (Date.now() < this.ignoreStaleUntilRealMs) return;
      this.onEvent(p, t);
    }
  }

  setFill(f, t, fromDevice = false) {
    if (this.fill >= 10 && f <= CFG.MIN_FILL_TO_COUNT) {
      if (fromDevice) {
        this.lowFillStreak++;
        if (this.lowFillStreak < CFG.BAG_OUT_CONFIRM_COUNT) {
          return 'held';
        }
      }
      const prevFill = Math.round(this.fill);
      this.lowFillStreak = 0;
      this.onBagOut(t, this.fill);
      enqueueCommand('C,RESET');
      this.saveState();
      this.evToast(`ごみを捨てたと判断しました（使用率 ${prevFill}%）`);
      return 'bagout';
    }
    this.lowFillStreak = 0;
    this.fill = f;
    this.addSample(t, f);
    return 'updated';
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
    this.lowFillStreak = 0;
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
    this.dA = this.emptyMm;
    this.dB = this.emptyMm;
    this.addSample(t, 0);
  }

  addSample(t, f) {
    if (this.hist.length === 0) {
      this.hist.push({ t, f });
      return;
    }
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

  computeRate(t) {
    const ws = Math.max(this.bagStart, t - 72 * HOUR_MS);
    const spanH = (t - ws) / HOUR_MS;
    const f0 = (ws === this.bagStart) ? 0 : this.fillAt(ws);
    const fNow = (t < vNow) ? this.fillAt(t) : this.fill;
    const cur = spanH > 0 ? (fNow - f0) / spanH : 0;

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
  }

  update(t, demoAutoBagOut = false) {
    let nd = nextDeadline(this.lastDeadline);
    while (nd <= t) {
      const fAtNd = this.fillAt(nd);
      this.computeRate(nd);
      const ndNext = nextDeadline(nd);
      const projNext = (this.rate > 0) ? (fAtNd + (this.rate * (ndNext - nd)) / HOUR_MS) : -1;
      const shouldTakeOut = (fAtNd >= 90) || (fAtNd >= CFG.MIN_FILL_TO_COUNT && projNext >= 100);

      if (demoAutoBagOut && shouldTakeOut) {
        const prevFill = Math.round(fAtNd);
        demoSkew = 0;
        this.onBagOut(nd, fAtNd);
        this.saveState();
        syncDemoDeviceIfNeeded();
        this.pushToast(`収集日（${md(nd)} ${hm(nd)}）に袋を出しました（使用率 ${prevFill}%）`);
      } else if (!this.bagOutSinceDeadline && fAtNd >= CFG.MIN_FILL_TO_COUNT) {
        this.savedBags++;
        this.addLog(nd, '収集日を見送り → 袋1枚節約');
        if (demoAutoBagOut) {
          this.pushToast(`収集日（${md(nd)} ${hm(nd)}）を見送り → 袋1枚節約`);
        }
      }
      this.bagOutSinceDeadline = false;
      this.lastDeadline = nd;
      nd = ndNext;
    }

    this.computeRate(t);

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
    } else if (this.fillAtD2 >= 100) {
      this.decision = D_TAKE;
      this.headline = takeLine;
      this.sub = `${w2}まで待つと、あふれる見込みです（約 ${Math.round(Math.min(this.fillAtD2, 199))}%）。`;
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
    if (this.hist.length === 0) return 0;
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

  distOf(pct) {
    return Math.round(this.emptyMm - (pct / 100.0) * (this.emptyMm - this.fullMm));
  }

  saveState() {
    const obj = {
      savedAtVNow: vNow,
      startMs: this.startMs,
      bagStart: this.bagStart,
      lastDeadline: this.lastDeadline,
      bagOutSinceDeadline: this.bagOutSinceDeadline,
      emptyMm: this.emptyMm,
      fullMm: this.fullMm,
      savedBags: this.savedBags,
      usedBags: this.usedBags,
      outFillSum: this.outFillSum,
      prevBagRate: this.prevBagRate,
      hist: this.hist
    };
    try {
      const tmp = STATE_FILE + '.tmp';
      fs.writeFileSync(tmp, JSON.stringify(obj));
      fs.renameSync(tmp, STATE_FILE);
    } catch (e) {}
  }

  loadState(nowMs) {
    if (!fs.existsSync(STATE_FILE)) return;
    try {
      const j = JSON.parse(fs.readFileSync(STATE_FILE, 'utf8'));
      const maxAllowedT = nowMs + 5 * MIN_MS;
      const lastHistT = (Array.isArray(j.hist) && j.hist.length > 0) ? j.hist[j.hist.length - 1].t : 0;
      if ((j.startMs && j.startMs > maxAllowedT) ||
          (j.bagStart && j.bagStart > maxAllowedT) ||
          (lastHistT > maxAllowedT) ||
          (j.savedAtVNow && j.savedAtVNow > maxAllowedT)) {
        console.warn('state.json has future fast-forward timestamps; resetting to clean state.');
        try { fs.unlinkSync(STATE_FILE); } catch (e) {}
        return;
      }

      if (Number.isInteger(j.emptyMm) && Number.isInteger(j.fullMm) && j.emptyMm > j.fullMm && j.fullMm > 0) {
        this.emptyMm = j.emptyMm;
        this.fullMm = j.fullMm;
      }
      this.startMs = j.startMs || this.startMs;
      this.bagStart = j.bagStart || this.bagStart;
      this.bagOutSinceDeadline = Boolean(j.bagOutSinceDeadline);
      this.savedBags = j.savedBags || 0;
      this.usedBags = j.usedBags || 0;
      this.outFillSum = j.outFillSum || 0;
      this.prevBagRate = (typeof j.prevBagRate === 'number') ? j.prevBagRate : -1;
      if (Array.isArray(j.hist) && j.hist.length > 0) {
        this.hist = j.hist;
        this.fill = this.hist[this.hist.length - 1].f;
      }
      this.lastDeadline = (typeof j.lastDeadline === 'number' && j.lastDeadline <= nowMs && j.lastDeadline >= nowMs - 15 * DAY_MS)
        ? j.lastDeadline
        : nowMs;
    } catch (e) {
      console.error('state.json load error:', e);
    }
  }
}

// ================= モデル初期化 =================
let model = new Model(vNow);
model.loadState(vNow);
model.update(vNow);

function isDeviceAlive() {
  return (Date.now() - model.lastRxRealMs) < 6000;
}

function getMode() {
  if (!isDeviceAlive()) return 'demo_web';
  return model.deviceKind === 'demo' ? 'demo_arduino' : 'real';
}

function isDemoMode() {
  return getMode() !== 'real';
}

function enqueueCommand(cmd) {
  if (!isDeviceAlive()) return;
  const now = Date.now();
  const isAuto = cmd.startsWith('C,AUTO,');
  const isSync = cmd.startsWith('C,SYNC,');
  commandQueue = commandQueue.filter(item =>
    (now - item.at) < CMD_TTL_MS &&
    item.cmd !== cmd &&
    !(isAuto && item.cmd.startsWith('C,AUTO,')) &&
    !(isSync && item.cmd.startsWith('C,SYNC,'))
  );
  commandQueue.push({ cmd, at: now });
}

function dequeueCommand() {
  const now = Date.now();
  while (commandQueue.length > 0) {
    const item = commandQueue.shift();
    if ((now - item.at) < CMD_TTL_MS) return item.cmd;
  }
  return 'OK';
}

function syncDemoDeviceIfNeeded() {
  if (getMode() === 'demo_arduino') {
    const dA = model.dA >= 0 ? Math.round(model.dA) : model.emptyMm;
    const dB = model.dB >= 0 ? Math.round(model.dB) : model.emptyMm;
    enqueueCommand(`C,SYNC,${Math.round(model.fill)},${model.lid},${dA},${dB}`);
  }
}

function scheduleNextDemoThrow(nowReal, nowV) {
  if (timeScale <= 1) {
    nextDemoThrowRealMs = nowReal + (12000 + Math.random() * 4000);
  } else if (timeScale <= 60) {
    nextDemoThrowRealMs = nowReal + (6000 + Math.random() * 2000);
  } else {
    nextDemoThrowVMs = nowV + (3.5 + Math.random() * 2.0) * HOUR_MS;
  }
}

function performDemoThrow(t, manual = false) {
  if (model.fill >= 100) {
    if (manual) {
      model.pushToast('すでに満杯（100%）です。「袋を出した (R)」で空にできます');
    }
    return false;
  }
  const beforeFill = model.fill;
  let addPct;
  if (manual) {
    addPct = Math.floor(6 + Math.random() * 9);
  } else if (timeScale <= 60) {
    addPct = Math.floor(5 + Math.random() * 4);
  } else {
    addPct = 2 + Math.floor(Math.random() * 3);
  }
  const afterFill = Math.min(100, beforeFill + addPct);
  const baseDist = model.distOf(afterFill);
  demoSkew = Math.max(-18, Math.min(18, demoSkew + Math.round(Math.random() * 16 - 8)));

  model.dA = Math.min(model.emptyMm, Math.max(model.fullMm, baseDist - demoSkew));
  model.dB = Math.min(model.emptyMm, Math.max(model.fullMm, baseDist + demoSkew));
  simLidUntilRealMs = Date.now() + (timeScale >= 21600 ? 400 : 1500);
  model.lid = 2;

  model.setFill(afterFill, t, false);
  model.onEvent(
    ['E', String(Date.now()), 'THROW', String(model.distOf(beforeFill)), String(baseDist)],
    t
  );
  if (afterFill >= 100 && beforeFill < 100) {
    model.onEvent(['E', String(Date.now()), 'FULL', '100', '0'], t);
  }
  syncDemoDeviceIfNeeded();
  return true;
}

// 100msごとに時計とモデルを更新
setInterval(() => {
  const nowReal = Date.now();
  const dt = nowReal - lastTickRealMs;
  lastTickRealMs = nowReal;

  if (timeScale <= 1) {
    if (Math.abs(vNow - nowReal) > 5000 && vNow <= nowReal) {
      vNow = nowReal;
    } else {
      vNow += dt;
    }
  } else {
    vNow += dt * timeScale;
  }

  const demo = isDemoMode();
  if (demo) {
    const prevLid = model.lid;
    model.lid = nowReal < simLidUntilRealMs ? 2 : 0;
    if (prevLid !== model.lid) {
      syncDemoDeviceIfNeeded();
    }

    if (model.fill < 100) {
      if (timeScale <= 60) {
        if (nowReal >= nextDemoThrowRealMs) {
          performDemoThrow(vNow, false);
          scheduleNextDemoThrow(nowReal, vNow);
        }
      } else {
        let guard = 0;
        while (nextDemoThrowVMs <= vNow && model.fill < 100 && guard < 4) {
          const throwT = nextDemoThrowVMs;
          model.update(throwT, true);
          if (model.fill < 100) {
            performDemoThrow(throwT, false);
          }
          scheduleNextDemoThrow(nowReal, throwT);
          guard++;
        }
        if (nextDemoThrowVMs <= vNow) {
          scheduleNextDemoThrow(nowReal, vNow);
        }
      }
    } else {
      scheduleNextDemoThrow(nowReal, vNow);
    }
  }

  model.update(vNow, demo);
  if (timeScale > 1) {
    model.addSample(vNow, model.fill);
  }

  if (nowReal - lastSaveRealMs > 60000) {
    model.saveState();
    lastSaveRealMs = nowReal;
  }
}, 100);

// ================= HTTP エンドポイント =================
app.get('/healthz', (req, res) => {
  res.status(200).json({ ok: true, alive: isDeviceAlive(), mode: getMode(), uptimeSec: Math.round(process.uptime()) });
});

app.post('/api/line', (req, res) => {
  const line = (req.body || '').trim();
  if (line) {
    model.handleLine(line, vNow);
  }
  const nextCmd = dequeueCommand();
  res.type('text/plain').send(nextCmd);
});

app.post('/api/action', (req, res) => {
  let payload = {};
  try { payload = JSON.parse(req.body); } catch (e) {}
  const { act, val } = payload;
  const mode = getMode();
  const demo = mode !== 'real';

  if (act === 'THROW') {
    if (!demo) {
      model.pushToast('実機接続中はデモ投入ボタンは使えません');
    } else if (performDemoThrow(vNow, true)) {
      scheduleNextDemoThrow(Date.now(), vNow);
    }
  } else if (act === 'RESET') {
    if (!demo) {
      model.pushToast('実機接続中はデモ用の袋交換ボタンは使えません');
    } else {
      const prevFill = Math.round(model.fill);
      simLidUntilRealMs = 0;
      model.lid = 0;
      demoSkew = 0;
      model.onBagOut(vNow, model.fill);
      model.saveState();
      scheduleNextDemoThrow(Date.now(), vNow);
      syncDemoDeviceIfNeeded();
      model.pushToast(
        prevFill >= CFG.MIN_FILL_TO_COUNT
          ? `袋を出しました（使用率 ${prevFill}%・0%から再スタート）`
          : '袋を新しくしました（0%から再スタート）'
      );
    }
  } else if (act === 'OPEN') {
    if (!demo) {
      enqueueCommand('C,OPEN');
    } else {
      simLidUntilRealMs = Date.now() + 2500;
      model.lid = 2;
      syncDemoDeviceIfNeeded();
      model.pushToast('フタを開けました（デモ）');
    }
  } else if (act === 'CLOSE') {
    if (!demo) {
      enqueueCommand('C,CLOSE');
    } else {
      simLidUntilRealMs = 0;
      model.lid = 0;
      syncDemoDeviceIfNeeded();
      model.pushToast('フタを閉じました（デモ）');
    }
  } else if (act === 'CAL_EMPTY') {
    if (mode === 'real') {
      enqueueCommand('C,CAL,EMPTY');
      model.pushToast('いまの距離を「空」の基準にしました');
    } else {
      model.pushToast('実機接続時のみ基準設定できます');
    }
  } else if (act === 'CAL_FULL') {
    if (mode === 'real') {
      enqueueCommand('C,CAL,FULL');
      model.pushToast('いまの距離を「満杯」の基準にしました');
    } else {
      model.pushToast('実機接続時のみ基準設定できます');
    }
  } else if (act === 'AUTO') {
    if (mode === 'real') {
      autoLid = !autoLid;
      enqueueCommand(`C,AUTO,${autoLid ? 1 : 0}`);
      model.pushToast(autoLid ? '自動開閉 ON' : '自動開閉 OFF');
    } else {
      model.pushToast('実機接続時のみ自動開閉を切り替えられます');
    }
  } else if (act === 'SPEED') {
    const idx = Math.min(SPEED_SCALES.length - 1, Math.max(0, Number(val) || 0));
    timeScale = SPEED_SCALES[idx];
    scheduleNextDemoThrow(Date.now(), vNow);
    model.pushToast(`時間の速さ：${SPEED_NAMES[idx]}`);
  } else if (act === 'RESET_CLOCK') {
    timeScale = 1;
    vNow = Date.now();
    commandQueue = [];
    demoSkew = 0;
    simLidUntilRealMs = 0;
    const keepEmpty = model.emptyMm;
    const keepFull = model.fullMm;
    const keepKind = model.deviceKind;
    const keepLastRx = model.lastRxRealMs;
    const keepHello = model.hello;
    model = new Model(vNow);
    model.emptyMm = keepEmpty;
    model.fullMm = keepFull;
    model.deviceKind = keepKind;
    model.lastRxRealMs = keepLastRx;
    model.hello = keepHello;
    model.update(vNow, false);
    model.saveState();
    scheduleNextDemoThrow(Date.now(), vNow);
    if (mode === 'real') {
      enqueueCommand('C,RESET');
      model.ignoreStaleUntilRealMs = Date.now() + 4000;
    } else if (mode === 'demo_arduino') {
      syncDemoDeviceIfNeeded();
    }
    model.pushToast('時計と記録を0からリセットしました');
  }

  res.json({ ok: true });
});

app.get('/api/state', (req, res) => {
  const nowReal = Date.now();
  const bagYen = CFG.BAG_LITERS * CFG.YEN_PER_LITER;
  const yenSaved = model.savedBags * bagYen;
  const plasticG = model.savedBags * CFG.BAG_GRAMS;
  const co2G = plasticG * CFG.CO2_PER_G_PE;
  const avgUse = model.usedBags > 0 ? model.outFillSum / model.usedBags : -1;
  const daysTracked = (vNow - model.startMs) / DAY_MS;
  const annualBags = daysTracked >= 7 ? (model.savedBags / daysTracked) * 365 : -1;

  res.json({
    cfg: CFG,
    autoLid,
    timeScale,
    vNow,
    alive: isDeviceAlive(),
    mode: getMode(),
    isDemo: isDemoMode(),
    errActive: (model.errCode > 0 && nowReal - model.errRealMs < 15000) ? model.errCode : 0,
    model: {
      emptyMm: model.emptyMm,
      fullMm: model.fullMm,
      fill: model.fill,
      dA: model.dA,
      dB: model.dB,
      pctA: model.pctOf(model.dA),
      pctB: model.pctOf(model.dB),
      lid: model.lid,
      rate: model.rate,
      rateSrc: model.rateSrc,
      d1: model.d1,
      d2: model.d2,
      tFull: model.tFull,
      decision: model.decision,
      isAction: model.isAction(),
      targetPickup: model.targetPickup(),
      headline: model.headline,
      sub: model.sub,
      savedBags: model.savedBags,
      usedBags: model.usedBags,
      bagYen,
      yenSaved,
      plasticG,
      co2G,
      avgUse,
      daysTracked,
      annualBags,
      lastThrowT: model.lastThrowT,
      lastThrowPct: model.lastThrowPct,
      hist: model.hist,
      toasts: model.toasts.filter(t => nowReal - t.at < 2800)
    }
  });
});

app.listen(PORT, () => console.log(`Smart Bin Server listening on port ${PORT}`));
