/* 建材數量估算 — 計算核心 (DXF 解析 / 圖元展開 / 房間偵測 / 數量計算)
 * 純 JavaScript,瀏覽器與 Node 皆可執行。 */
(function (root) {
'use strict';

/* ------------------------------------------------------------------ */
/* 1. 文字解碼                                                          */
/* ------------------------------------------------------------------ */
const decoders = {};
function getDecoder(enc) {
  if (!decoders[enc]) {
    try { decoders[enc] = new TextDecoder(enc, { fatal: false }); }
    catch (e) { decoders[enc] = new TextDecoder('utf-8'); }
  }
  return decoders[enc];
}
const CP_MAP = { ANSI_950: 'big5', ANSI_936: 'gbk', ANSI_932: 'shift_jis', ANSI_949: 'euc-kr', ANSI_1252: 'windows-1252' };

// bytes: Uint8Array slice. enc: 'utf-8' | 'big5' ...
function decodeBytes(bytes, enc) {
  // 是否含 \U+XXXX
  let hasU = false;
  for (let i = 0; i + 2 < bytes.length; i++) {
    if (bytes[i] === 92 && (bytes[i + 1] === 85 || bytes[i + 1] === 117) && bytes[i + 2] === 43) { hasU = true; break; }
  }
  if (!hasU) return getDecoder(enc).decode(bytes);
  // 把 \U+00XX (XX>=80) 還原為位元組 (部分轉檔器會這樣寫 Big5),其餘 \U+XXXX 轉成 Unicode
  let out = '';
  let buf = [];
  const flush = () => { if (buf.length) { out += getDecoder(enc).decode(new Uint8Array(buf)); buf = []; } };
  for (let i = 0; i < bytes.length; i++) {
    const b = bytes[i];
    if (b === 92 && i + 6 < bytes.length + 0 && (bytes[i + 1] === 85 || bytes[i + 1] === 117) && bytes[i + 2] === 43) {
      const hex = String.fromCharCode(bytes[i + 3], bytes[i + 4], bytes[i + 5], bytes[i + 6]);
      if (/^[0-9a-fA-F]{4}$/.test(hex)) {
        const cp = parseInt(hex, 16);
        if (cp >= 0x80 && cp <= 0xff && enc !== 'utf-8') { buf.push(cp); }
        else { flush(); out += String.fromCharCode(cp); }
        i += 6; continue;
      }
    }
    buf.push(b);
  }
  flush();
  return out;
}

function cleanMText(s) {
  if (!s) return '';
  s = s.replace(/\\P/g, '\n').replace(/\\~/g, ' ');
  s = s.replace(/\\[ACFHQTWfhqtwac][^;\\{}]*;/g, '');
  s = s.replace(/\\S([^;]*);/g, (m, a) => a.replace(/[#^\/]/, '/'));
  s = s.replace(/\\[LlOoKk]/g, '');
  s = s.replace(/[{}]/g, '');
  s = s.replace(/%%[cC]/g, 'Ø').replace(/%%[dD]/g, '°').replace(/%%[pP]/g, '±').replace(/%%[uUoO]/g, '');
  return s.trim();
}

/* ------------------------------------------------------------------ */
/* 2. DXF 解析 (位元組串流,支援大型檔案)                                 */
/* ------------------------------------------------------------------ */
function parseDXF(u8, onProgress) {
  const n = u8.length;
  let pos = 0;
  // 先找 HEADER 取得版本與碼頁
  let enc = 'utf-8';
  {
    const head = new TextDecoder('latin1').decode(u8.subarray(0, Math.min(n, 200000)));
    const mv = /\$ACADVER\s*\r?\n\s*1\s*\r?\n\s*(AC\d+)/.exec(head);
    const mc = /\$DWGCODEPAGE\s*\r?\n\s*3\s*\r?\n\s*(\S+)/.exec(head);
    const ver = mv ? mv[1] : 'AC1021';
    if (ver < 'AC1021' && mc && CP_MAP[mc[1].toUpperCase()]) enc = CP_MAP[mc[1].toUpperCase()];
  }
  function readLine() {
    if (pos >= n) return null;
    let s = pos;
    let e = u8.indexOf(10, pos);
    if (e < 0) e = n;
    pos = e + 1;
    let ee = e;
    if (ee > s && u8[ee - 1] === 13) ee--;
    return [s, ee];
  }
  function trimRange(r) {
    let s = r[0], e = r[1];
    while (s < e && (u8[s] === 32 || u8[s] === 9)) s++;
    while (e > s && (u8[e - 1] === 32 || u8[e - 1] === 9)) e--;
    return [s, e];
  }
  function intOf(r) { let v = 0, neg = false, i = r[0]; if (u8[i] === 45) { neg = true; i++; } for (; i < r[1]; i++) { const c = u8[i]; if (c < 48 || c > 57) break; v = v * 10 + (c - 48); } return neg ? -v : v; }
  const latin = new TextDecoder('latin1');
  function strOf(r) { return latin.decode(u8.subarray(r[0], r[1])); }
  function txtOf(r) { return decodeBytes(u8.subarray(r[0], r[1]), enc); }

  // 讀取所有 group pairs,但只在需要時解碼
  const header = {};
  const layers = {};
  const blocks = {};
  const entities = [];
  let section = null;
  let cur = null;         // 目前實體 {type, g:[[code,val],...]}
  let curBlock = null;
  let lastProgress = 0;
  let inHeaderVar = null;
  let tableType = null, tableEntry = null;
  const TEXT_CODES = new Set([1, 2, 3, 8, 7]);

  function finishEntity() {
    if (!cur) return;
    const e = cur; cur = null;
    if (section === 'ENTITIES') entities.push(e);
    else if (section === 'BLOCKS' && curBlock) curBlock.ents.push(e);
  }

  while (true) {
    const cl = readLine(); if (!cl) break;
    const vl = readLine(); if (!vl) break;
    const code = intOf(trimRange(cl));
    const vr = code === 1 || code === 3 ? vl : trimRange(vl);
    if (onProgress && pos - lastProgress > 4e6) { lastProgress = pos; onProgress(pos / n); }
    if (code === 0) {
      const v = strOf(vr);
      if (v === 'SECTION') { finishEntity(); section = '?'; continue; }
      if (v === 'ENDSEC') { finishEntity(); section = null; continue; }
      if (v === 'EOF') break;
      if (section === 'TABLES') {
        if (tableEntry && tableEntry.type === 'LAYER' && tableEntry.name != null) layers[tableEntry.name] = tableEntry;
        tableEntry = (v === 'TABLE' || v === 'ENDTAB') ? null : { type: v, name: null };
        continue;
      }
      if (section === 'BLOCKS') {
        if (v === 'BLOCK') { finishEntity(); curBlock = { name: null, base: [0, 0], ents: [], _hdr: true }; continue; }
        if (v === 'ENDBLK') { finishEntity(); if (curBlock && curBlock.name != null) blocks[curBlock.name] = curBlock; curBlock = null; cur = { type: 'ENDBLK', g: [], skip: true }; continue; }
      }
      if (section === 'ENTITIES' || section === 'BLOCKS') {
        if (cur && cur.skip) cur = null;
        if (curBlock) curBlock._hdr = false;
        finishEntity();
        cur = { type: v, g: [] };
      }
      continue;
    }
    if (section === '?') { if (code === 2) section = strOf(vr); continue; }
    if (section === 'HEADER') {
      if (code === 9) { inHeaderVar = strOf(vr); continue; }
      if (inHeaderVar) { header[inHeaderVar] = header[inHeaderVar] || {}; header[inHeaderVar][code] = strOf(vr); }
      continue;
    }
    if (section === 'TABLES') {
      if (tableEntry && tableEntry.type === 'LAYER') {
        if (code === 2) tableEntry.name = txtOf(vr);
        else if (code === 62) tableEntry.color = intOf(vr);
        else if (code === 70) tableEntry.flags = intOf(vr);
      }
      continue;
    }
    if (section === 'BLOCKS' && curBlock && curBlock._hdr && !cur) {
      if (code === 2) curBlock.name = txtOf(vr);
      else if (code === 10) curBlock.base[0] = parseFloat(strOf(vr));
      else if (code === 20) curBlock.base[1] = parseFloat(strOf(vr));
      continue;
    }
    if (cur && !cur.skip) {
      if (TEXT_CODES.has(code)) cur.g.push(code, txtOf(vr));
      else if (code >= 10 && code < 60 || code >= 210 && code < 240 || code >= 1010 && code < 1060) cur.g.push(code, parseFloat(strOf(vr)));
      else if (code >= 60 && code < 100 || code >= 280 && code < 300 || code >= 370 && code < 390) cur.g.push(code, intOf(vr));
      // 其他 code 略過
    }
  }
  finishEntity();
  if (tableEntry && tableEntry.type === 'LAYER' && tableEntry.name != null) layers[tableEntry.name] = tableEntry;
  const ins = header.$INSUNITS ? parseInt(header.$INSUNITS[70]) : 0;
  return { header, layers, blocks, entities, insunits: ins, encoding: enc };
}

/* 實體 group list 取值工具 */
function gv(g, code, def) { for (let i = 0; i < g.length; i += 2) if (g[i] === code) return g[i + 1]; return def; }

/* ------------------------------------------------------------------ */
/* 3. 圖元展開(INSERT 遞迴、OCS、弧線離散)                              */
/* ------------------------------------------------------------------ */
// 矩陣 [a,b,c,d,e,f] : x' = a x + b y + c ; y' = d x + e y + f
function mmul(A, B) { return [A[0] * B[0] + A[1] * B[3], A[0] * B[1] + A[1] * B[4], A[0] * B[2] + A[1] * B[5] + A[2], A[3] * B[0] + A[4] * B[3], A[3] * B[1] + A[4] * B[4], A[3] * B[2] + A[4] * B[5] + A[5]]; }
const ID = [1, 0, 0, 0, 1, 0];

function arcPts(cx, cy, r, a0, a1, out, M, ocsFlip) {
  if (a1 < a0) a1 += Math.PI * 2;
  const k = Math.max(3, Math.min(64, Math.ceil((a1 - a0) / (Math.PI / 16))));
  for (let i = 0; i <= k; i++) {
    const a = a0 + (a1 - a0) * i / k;
    let x = cx + r * Math.cos(a), y = cy + r * Math.sin(a);
    if (ocsFlip) x = -x;
    out.push(M[0] * x + M[1] * y + M[2], M[3] * x + M[4] * y + M[5]);
  }
}
function bulgeTo(x1, y1, x2, y2, b, out) {
  // 加入 (x1,y1)->(x2,y2) 的中間點(不含終點)
  const th = 4 * Math.atan(b);
  const dx = x2 - x1, dy = y2 - y1, c = Math.hypot(dx, dy);
  if (c === 0 || Math.abs(b) < 1e-9) return;
  const r = c / (2 * Math.sin(th / 2));
  const h = r * Math.cos(th / 2);
  const mx = (x1 + x2) / 2, my = (y1 + y2) / 2;
  const cx = mx - dy / c * h, cy = my + dx / c * h;
  const a0 = Math.atan2(y1 - cy, x1 - cx);
  const k = Math.max(2, Math.min(32, Math.ceil(Math.abs(th) / (Math.PI / 16))));
  const R = Math.abs(r);
  for (let i = 1; i < k; i++) {
    const a = a0 + th * i / k;
    out.push(cx + R * Math.cos(a), cy + R * Math.sin(a));
  }
}

/* HATCH 邊界:回傳多個封閉迴圈 (局部座標 x,y,...) */
function parseHatchLoops(g) {
  let k = -1;
  for (let i = 0; i < g.length; i += 2) if (g[i] === 91) { k = i; break; }
  if (k < 0) return [];
  const np = g[k + 1]; let i = k + 2; const loops = [];
  const n = g.length;
  for (let p = 0; p < np && i < n; p++) {
    while (i < n && g[i] !== 92) i += 2;
    if (i >= n) break;
    const flag = g[i + 1]; i += 2;
    const pts = [];
    if (flag & 2) {
      let hasB = 0;
      if (g[i] === 72) { hasB = g[i + 1]; i += 2; }
      if (g[i] === 73) i += 2;
      if (g[i] === 93) i += 2;
      const vx = [], vy = [], vb = [];
      while (i < n && g[i] !== 97 && g[i] !== 92) {
        if (g[i] === 10) { vx.push(g[i + 1]); vb.push(0); } else if (g[i] === 20) vy.push(g[i + 1]); else if (g[i] === 42 && vb.length) vb[vb.length - 1] = g[i + 1];
        i += 2;
      }
      for (let j = 0; j < Math.min(vx.length, vy.length); j++) {
        pts.push(vx[j], vy[j]);
        const jn = (j + 1) % vx.length;
        if (vb[j]) bulgeTo(vx[j], vy[j], vx[jn], vy[jn], vb[j], pts);
      }
    } else {
      if (g[i] === 93) i += 2;
      while (i < n && g[i] === 72) {
        const et = g[i + 1]; i += 2;
        const e = {};
        const cps = [];
        while (i < n && g[i] !== 72 && g[i] !== 97 && g[i] !== 92) {
          const c = g[i], v = g[i + 1];
          if (et === 4) { if (c === 10) cps.push([v, 0]); else if (c === 20 && cps.length) cps[cps.length - 1][1] = v; }
          else if (!(c in e)) e[c] = v;
          i += 2;
        }
        if (et === 1) { if (!pts.length) pts.push(e[10], e[20]); pts.push(e[11], e[21]); }
        else if (et === 2 || et === 3) {
          const cx = e[10], cy = e[20];
          let a0 = (e[50] || 0) * Math.PI / 180, a1 = (e[51] === undefined ? 360 : e[51]) * Math.PI / 180;
          const ccw = e[73] === undefined ? 1 : e[73];
          let mx, my, ra;
          if (et === 2) { mx = e[40]; my = 0; ra = 1; } else { mx = e[11]; my = e[21]; ra = e[40] || 1; }
          if (!ccw) { a0 = -a0; a1 = -a1; }
          let sweep = a1 - a0;
          if (ccw && sweep < 0) sweep += Math.PI * 2;
          if (!ccw && sweep > 0) sweep -= Math.PI * 2;
          const kk = Math.max(4, Math.min(48, Math.ceil(Math.abs(sweep) / (Math.PI / 16))));
          for (let j = 0; j <= kk; j++) {
            const a = a0 + sweep * j / kk;
            pts.push(cx + mx * Math.cos(a) - my * ra * Math.sin(a), cy + my * Math.cos(a) + mx * ra * Math.sin(a));
          }
        } else if (et === 4) { for (const q of cps) pts.push(q[0], q[1]); }
      }
    }
    if (pts.length >= 6) loops.push(pts);
  }
  return loops;
}

/* 展開為:
 * polys: [{L:layerIdx, p:Float64Array(x,y,...), c:closed, ins:insertId}]
 * texts: [{L, x, y, h, s}]
 * inserts: [{L, name, parent, box:[minx,miny,maxx,maxy](world), w, h (local size*scale), cx, cy}]
 */
function flattenDXF(doc, onProgress) {
  const layerNames = [];
  const layerIdx = new Map();
  function LI(name) { let i = layerIdx.get(name); if (i === undefined) { i = layerNames.length; layerNames.push(name); layerIdx.set(name, i); } return i; }
  const polys = [], texts = [], inserts = [], hatches = [];
  const bboxCache = new Map();

  function localBBox(name, depth) {
    if (bboxCache.has(name)) return bboxCache.get(name);
    bboxCache.set(name, null);
    const b = doc.blocks[name];
    if (!b) return null;
    let bb = [Infinity, Infinity, -Infinity, -Infinity];
    const tmp = { polys: [], texts: [], inserts: [] };
    emitEntities(b.ents, ID, null, depth + 1, -1, tmp, true);
    for (const p of tmp.polys) for (let i = 0; i < p.p.length; i += 2) { const x = p.p[i], y = p.p[i + 1]; if (x < bb[0]) bb[0] = x; if (y < bb[1]) bb[1] = y; if (x > bb[2]) bb[2] = x; if (y > bb[3]) bb[3] = y; }
    if (!isFinite(bb[0])) bb = null;
    bboxCache.set(name, bb);
    return bb;
  }

  function push(out, L, arr, closed, ins) {
    if (arr.length < 4) return;
    out.polys.push({ L, p: Float64Array.from(arr), c: closed, ins });
  }

  function emitEntities(ents, M, inhLayer, depth, insId, out, bboxOnly) {
    if (depth > 16) return;
    for (const e of ents) {
      const g = e.g;
      let lay = gv(g, 8, '0');
      if ((lay === '0' || lay === '') && inhLayer != null) lay = inhLayer;
      const L = bboxOnly ? 0 : LI(lay);
      const ez = gv(g, 230, 1);
      const flip = ez < 0;
      const T = (x, y) => { if (flip) x = -x; return [M[0] * x + M[1] * y + M[2], M[3] * x + M[4] * y + M[5]]; };
      const t = e.type;
      if (t === 'LINE') {
        const a = [gv(g, 10, 0), gv(g, 20, 0)], b = [gv(g, 11, 0), gv(g, 21, 0)];
        const p1 = [M[0] * a[0] + M[1] * a[1] + M[2], M[3] * a[0] + M[4] * a[1] + M[5]];
        const p2 = [M[0] * b[0] + M[1] * b[1] + M[2], M[3] * b[0] + M[4] * b[1] + M[5]];
        push(out, L, [p1[0], p1[1], p2[0], p2[1]], false, insId);
      } else if (t === 'LWPOLYLINE') {
        const flag = gv(g, 70, 0); const closed = !!(flag & 1);
        const vx = [], vy = [], vb = [];
        for (let i = 0; i < g.length; i += 2) {
          if (g[i] === 10) { vx.push(g[i + 1]); vb.push(0); }
          else if (g[i] === 20) vy.push(g[i + 1]);
          else if (g[i] === 42 && vb.length) vb[vb.length - 1] = g[i + 1];
        }
        const pts = [];
        const nV = Math.min(vx.length, vy.length);
        for (let i = 0; i < nV; i++) {
          pts.push(vx[i], vy[i]);
          const j = i + 1 < nV ? i + 1 : (closed ? 0 : -1);
          if (j >= 0 && vb[i]) bulgeTo(vx[i], vy[i], vx[j], vy[j], vb[i], pts);
        }
        if (closed && nV > 2) pts.push(vx[0], vy[0]);
        const w = [];
        for (let i = 0; i < pts.length; i += 2) { const q = T(pts[i], pts[i + 1]); w.push(q[0], q[1]); }
        push(out, L, w, closed, insId);
      } else if (t === 'POLYLINE') {
        // 頂點在 e.verts (由 groupPolylines 收集)
        const flag = gv(g, 70, 0); const closed = !!(flag & 1);
        if (flag & (16 | 64)) continue; // mesh
        const vs = e.verts || [];
        const pts = [];
        for (let i = 0; i < vs.length; i++) {
          const v = vs[i]; pts.push(v[0], v[1]);
          const j = i + 1 < vs.length ? i + 1 : (closed ? 0 : -1);
          if (j >= 0 && v[2]) bulgeTo(v[0], v[1], vs[j][0], vs[j][1], v[2], pts);
        }
        if (closed && vs.length > 2) pts.push(vs[0][0], vs[0][1]);
        const w = [];
        const is3d = !!(flag & 8);
        for (let i = 0; i < pts.length; i += 2) { const q = is3d ? [M[0] * pts[i] + M[1] * pts[i + 1] + M[2], M[3] * pts[i] + M[4] * pts[i + 1] + M[5]] : T(pts[i], pts[i + 1]); w.push(q[0], q[1]); }
        push(out, L, w, closed, insId);
      } else if (t === 'ARC' || t === 'CIRCLE') {
        const cx = gv(g, 10, 0), cy = gv(g, 20, 0), r = gv(g, 40, 0);
        let a0 = 0, a1 = Math.PI * 2;
        if (t === 'ARC') { a0 = gv(g, 50, 0) * Math.PI / 180; a1 = gv(g, 51, 360) * Math.PI / 180; }
        const w = []; arcPts(cx, cy, r, a0, a1, w, M, flip);
        push(out, L, w, t === 'CIRCLE', insId);
      } else if (t === 'ELLIPSE') {
        const cx = gv(g, 10, 0), cy = gv(g, 20, 0), mx = gv(g, 11, 1), my = gv(g, 21, 0), ra = gv(g, 40, 1);
        let p0 = gv(g, 41, 0), p1 = gv(g, 42, Math.PI * 2); if (p1 < p0) p1 += Math.PI * 2;
        const k = Math.max(8, Math.min(64, Math.ceil((p1 - p0) / (Math.PI / 16))));
        const w = [];
        for (let i = 0; i <= k; i++) { const a = p0 + (p1 - p0) * i / k; const x = cx + mx * Math.cos(a) - my * ra * Math.sin(a); const y = cy + my * Math.cos(a) + mx * ra * Math.sin(a); const q = T(x, y); w.push(q[0], q[1]); }
        push(out, L, w, Math.abs(p1 - p0 - Math.PI * 2) < 1e-6, insId);
      } else if (t === 'SPLINE') {
        const fx = [], fy = [], cxs = [], cys = [];
        for (let i = 0; i < g.length; i += 2) { if (g[i] === 11) fx.push(g[i + 1]); else if (g[i] === 21) fy.push(g[i + 1]); else if (g[i] === 10) cxs.push(g[i + 1]); else if (g[i] === 20) cys.push(g[i + 1]); }
        const X = fx.length > 1 ? fx : cxs, Y = fx.length > 1 ? fy : cys;
        const w = []; for (let i = 0; i < Math.min(X.length, Y.length); i++) { const q = T(X[i], Y[i]); w.push(q[0], q[1]); }
        push(out, L, w, false, insId);
      } else if (t === 'SOLID' || t === '3DFACE') {
        const pts = [[gv(g, 10, 0), gv(g, 20, 0)], [gv(g, 11, 0), gv(g, 21, 0)], [gv(g, 13, 0), gv(g, 23, 0)], [gv(g, 12, 0), gv(g, 22, 0)]];
        const w = []; for (const p of pts) { const q = t === 'SOLID' ? T(p[0], p[1]) : [M[0] * p[0] + M[1] * p[1] + M[2], M[3] * p[0] + M[4] * p[1] + M[5]]; w.push(q[0], q[1]); }
        w.push(w[0], w[1]);
        push(out, L, w, true, insId);
      } else if (t === 'TEXT' || t === 'MTEXT' || t === 'ATTRIB') {
        if (bboxOnly) continue;
        let s = gv(g, 1, '');
        if (t === 'MTEXT') { let pre = ''; for (let i = 0; i < g.length; i += 2) if (g[i] === 3) pre += g[i + 1]; s = cleanMText(pre + s); }
        else s = cleanMText(s);
        if (!s) continue;
        let x = gv(g, 10, 0), y = gv(g, 20, 0);
        const ha = gv(g, 72, 0), va = gv(g, 73, 0);
        if (t !== 'MTEXT' && (ha || va)) { x = gv(g, 11, x); y = gv(g, 21, y); }
        const q = (t === 'MTEXT') ? [M[0] * x + M[1] * y + M[2], M[3] * x + M[4] * y + M[5]] : T(x, y);
        const h = gv(g, 40, 0) * Math.hypot(M[0], M[3]);
        // 估算文字中心:以字高 * 字數 粗估
        let cx = q[0], cy = q[1];
        if (t !== 'MTEXT') {
          const rot = gv(g, 50, 0) * Math.PI / 180;
          const len = s.length * h * 0.9;
          let off = 0.5; if (ha === 1 || ha === 4) off = 0; else if (ha === 2) off = -0.5; else if (ha === 0) off = 0.5;
          const ux = Math.cos(rot) * len * off, uy = Math.sin(rot) * len * off;
          const vx = -Math.sin(rot) * h * (va === 2 ? 0 : va === 3 ? -0.5 : 0.5), vy = Math.cos(rot) * h * (va === 2 ? 0 : va === 3 ? -0.5 : 0.5);
          cx = q[0] + (M[0] * ux + M[1] * uy) + (M[0] * vx + M[1] * vy);
          cy = q[1] + (M[3] * ux + M[4] * uy) + (M[3] * vx + M[4] * vy);
        } else {
          const ap = gv(g, 71, 1); const wdt = gv(g, 41, s.length * h) * Math.hypot(M[0], M[3]);
          const col = (ap - 1) % 3, row = Math.floor((ap - 1) / 3);
          cx = q[0] + (col === 0 ? wdt / 2 : col === 2 ? -wdt / 2 : 0) * Math.sign(M[0] || 1);
          cy = q[1] + (row === 0 ? -h / 2 : row === 2 ? h / 2 : 0);
        }
        texts.push({ L, x: cx, y: cy, h, s });
      } else if (t === 'HATCH') {
        if (bboxOnly) continue;
        const loops = parseHatchLoops(g);
        if (!loops.length) continue;
        const wl = loops.map(lp => { const o = new Float64Array(lp.length); for (let i = 0; i < lp.length; i += 2) { const q = T(lp[i], lp[i + 1]); o[i] = q[0]; o[i + 1] = q[1]; } return o; });
        let a = Infinity, b2 = Infinity, c = -Infinity, d = -Infinity;
        for (const lp of wl) for (let i = 0; i < lp.length; i += 2) { if (lp[i] < a) a = lp[i]; if (lp[i] > c) c = lp[i]; if (lp[i + 1] < b2) b2 = lp[i + 1]; if (lp[i + 1] > d) d = lp[i + 1]; }
        hatches.push({ L, pat: gv(g, 2, ''), loops: wl, bb: [a, b2, c, d], ins: insId });
      } else if (t === 'INSERT') {
        const name = gv(g, 2, '');
        const b = doc.blocks[name];
        if (!b || name.startsWith('*D')) { /* 標註圖塊略過 */ if (!b) continue; }
        if (name.startsWith('*D') || name.startsWith('*d')) continue;
        const sx = gv(g, 41, 1) || 1, sy = gv(g, 42, 1) || 1;
        const rot = gv(g, 50, 0) * Math.PI / 180;
        let px = gv(g, 10, 0), py = gv(g, 20, 0);
        const nc = Math.max(1, gv(g, 70, 1)), nr = Math.max(1, gv(g, 71, 1));
        const csp = gv(g, 44, 0), rsp = gv(g, 45, 0);
        const c = Math.cos(rot), s = Math.sin(rot);
        for (let ci = 0; ci < nc; ci++) for (let ri = 0; ri < nr; ri++) {
          const ox = px + c * ci * csp - s * ri * rsp, oy = py + s * ci * csp + c * ri * rsp;
          let Mi = [c * sx, -s * sy, 0, s * sx, c * sy, 0];
          Mi[2] = ox - (Mi[0] * b.base[0] + Mi[1] * b.base[1]);
          Mi[5] = oy - (Mi[3] * b.base[0] + Mi[4] * b.base[1]);
          if (flip) Mi = [-Mi[0], -Mi[1], -Mi[2], Mi[3], Mi[4], Mi[5]];
          const M2 = mmul(M, Mi);
          let id = -1;
          if (!bboxOnly) {
            const lb = localBBox(name, depth);
            let box = null, w = 0, h = 0;
            if (lb) {
              const cs = [[lb[0], lb[1]], [lb[2], lb[1]], [lb[2], lb[3]], [lb[0], lb[3]]].map(p => [M2[0] * p[0] + M2[1] * p[1] + M2[2], M2[3] * p[0] + M2[4] * p[1] + M2[5]]);
              box = cs;
              w = Math.hypot(cs[1][0] - cs[0][0], cs[1][1] - cs[0][1]);
              h = Math.hypot(cs[3][0] - cs[0][0], cs[3][1] - cs[0][1]);
            }
            id = inserts.length;
            inserts.push({ L, name, parent: insId, box, w, h, depth });
          }
          emitEntities(b.ents, M2, lay, depth + 1, bboxOnly ? -1 : id, out, bboxOnly);
          if (!bboxOnly) {
            // ATTRIB 在 INSERT 之後(屬於本實體)
            if (e.attribs) emitEntities(e.attribs, M, inhLayer, depth, insId, out, bboxOnly);
          }
        }
      }
    }
  }
  // 收集 POLYLINE/VERTEX/SEQEND 與 INSERT/ATTRIB
  function group(ents) {
    const out = [];
    let i = 0;
    while (i < ents.length) {
      const e = ents[i];
      if (e.type === 'POLYLINE') {
        e.verts = []; i++;
        while (i < ents.length && ents[i].type === 'VERTEX') { const g = ents[i].g; const fl = gv(g, 70, 0); if (!(fl & 16)) e.verts.push([gv(g, 10, 0), gv(g, 20, 0), gv(g, 42, 0)]); i++; }
        if (i < ents.length && ents[i].type === 'SEQEND') i++;
        out.push(e); continue;
      }
      if (e.type === 'INSERT') {
        i++;
        if (gv(e.g, 66, 0)) {
          e.attribs = [];
          while (i < ents.length && (ents[i].type === 'ATTRIB')) { e.attribs.push(ents[i]); i++; }
          if (i < ents.length && ents[i].type === 'SEQEND') i++;
        }
        out.push(e); continue;
      }
      if (e.type === 'VERTEX' || e.type === 'SEQEND' || e.type === 'ATTRIB' && false) { i++; continue; }
      out.push(e); i++;
    }
    return out;
  }
  for (const k in doc.blocks) doc.blocks[k].ents = group(doc.blocks[k].ents);
  const top = group(doc.entities);
  const out = { polys, texts, inserts };
  // 依頂層實體分批處理以便回報進度
  const chunk = 2000;
  for (let i = 0; i < top.length; i += chunk) {
    emitEntities(top.slice(i, i + chunk), ID, null, 0, -1, out, false);
    if (onProgress) onProgress(i / top.length);
  }
  // 計算 bbox
  for (const p of polys) {
    let a = Infinity, b = Infinity, c = -Infinity, d = -Infinity; const q = p.p;
    for (let i = 0; i < q.length; i += 2) { const x = q[i], y = q[i + 1]; if (x < a) a = x; if (y < b) b = y; if (x > c) c = x; if (y > d) d = y; }
    p.bb = [a, b, c, d];
  }
  return { layerNames, polys, texts, inserts, hatches };
}

/* ------------------------------------------------------------------ */
/* 4. 圖層角色自動判斷                                                   */
/* ------------------------------------------------------------------ */
const ROLES = {
  ignore: '忽略',
  wall_rc: 'RC牆',
  wall_brick: '磚牆',
  wall_block: '白磚/輕質磚',
  wall_light: '輕隔間(乾式)',
  column: '柱',
  beam: '梁(線)',
  door: '門',
  window: '窗',
  rail: '欄杆/矮牆',
  boundary: '邊界線(只圍房間)',
};
function guessRole(name) {
  const n = name.toUpperCase();
  const thk = (() => { const m = /(\d+(?:\.\d+)?)\s*CM/i.exec(name); if (m) return parseFloat(m[1]); const m2 = /(\d{2})\s*(?:RC|牆)/i.exec(name); return m2 ? parseFloat(m2[1]) : null; })();
  if (/DIM|尺寸|標註|TEXT|文字|WORD|說明|圖名|圖框|FRAME|HATCH|填充|家具|FURN|衛浴|TOILET|SANI|廚具|KITCH|冷氣|^AC$|GRID|格線|座標|軸|PATT|立面|ELEV|樹|PLANT|車|PARK|基地|地界|法定|面積|AREA|上色|DEFPOINTS|底圖|編號|NO\.|MARK|問題|SYMB|符號|LIFT|電梯|STAIR|樓梯|梯|天花|CEIL|設備|配電|PHAN|消防|燈|LIGHT|管|PIPE/i.test(name)
      && !/RC|磚|BRICK|WALL(?!-HATCH)/i.test(name)) {
    if (/欄杆|RAIL/i.test(name)) return { role: 'rail', thk: 10 };
    return { role: 'ignore' };
  }
  if (/HATCH/i.test(name)) return { role: 'ignore' };
  if (/白磚|輕質磚|輕質隔間磚|ALC|AAC/i.test(name)) return { role: 'wall_block', thk: thk || 10 };
  if (/磚|BRICK|0\.5B|1\.0B|1B/i.test(name)) { const t = thk || (/1\.?0?B/i.test(name) && !/0\.5B/i.test(name) ? 24 : 12); return { role: 'wall_brick', thk: t }; }
  if (/白磚|輕質磚|輕質隔間磚|輕質混凝土|ALC|AAC|BLOCK/i.test(name)) return { role: 'wall_block', thk: thk || 10 };
  if (/輕隔|乾式|石膏|GYP|LGS|DRYWALL/i.test(name)) return { role: 'wall_light', thk: thk || 10 };
  if (/RC|混凝土|CONC/i.test(n) && !/柱|COL|樑|梁|BEAM/i.test(name)) return { role: 'wall_rc', thk: thk || 15 };
  if (/WALL|牆/i.test(name)) return { role: 'wall_rc', thk: thk || 15 };
  if (/柱|COL/i.test(name) && !/編號|NO|TEXT|下層/i.test(name)) return { role: 'column' };
  if (/樑|梁|BEAM/i.test(name) && !/編號|NO|TEXT/i.test(name)) return { role: 'beam' };
  if (/門|DOOR|DR/i.test(name) && !/MARK|編號/i.test(name)) return { role: 'door' };
  if (/窗|WIN|WD/i.test(name)) return { role: 'window' };
  if (/欄杆|RAIL|女兒牆|PARAPET/i.test(name)) return { role: 'rail', thk: 10 };
  return { role: 'ignore' };
}

/* ------------------------------------------------------------------ */
/* 5. 空間類型                                                          */
/* ------------------------------------------------------------------ */
const ROOM_TYPES = [
  { id: 'wet', name: '浴廁', re: /浴|廁|衛|盥洗|淋浴|WC|化妝室|洗手間|BATH|TOILET/i },
  { id: 'kitchen', name: '廚房', re: /廚|KITCHEN/i },
  { id: 'balcony', name: '陽台/露台', re: /陽台|露台|平台|曬衣|花台|BALCONY|TERRACE/i },
  { id: 'public', name: '公共空間', re: /梯廳|電梯廳|走廊|走道|大廳|門廳|玄關|安全梯|樓梯|梯間|LOBBY|HALL|CORRIDOR|騎樓|通道/i },
  { id: 'living', name: '居室', re: /客廳|餐廳|臥|起居|書房|和室|房間|多功能|儲藏|儲物|更衣|工作室|辦公|會議|店舖|店鋪|商場|LIVING|DINING|BED|ROOM|OFFICE|STORE/i },
  { id: 'service', name: '機房/設備', re: /機房|機電|設備|配電|水箱|發電|垃圾|管道|車道|停車|PS|EPS|WPS|MECH/i },
];
function mergedType(r) {
  const ts = (r.names || [r.name]).map(roomTypeOf).filter(Boolean);
  if (!ts.length) return 'living';
  if (ts.length > 1) for (const p of ['living', 'public', 'kitchen', 'wet', 'balcony', 'service']) if (ts.indexOf(p) >= 0) return p;
  return ts[0];
}
function roomTypeOf(s) { for (const t of ROOM_TYPES) if (t.re.test(s)) return t.id; return null; }
function isRoomLabel(s) {
  if (!s || s.length > 12) return false;
  if (/平面圖|單線圖|比例|A1|A3|=|＝|H=|cm|CM|kg|\d{2,}/.test(s)) return false;
  return roomTypeOf(s) !== null;
}

/* 預設裝修設定(每種空間) */
function defaultFinishes() {
  return {
    wet:     { floor: 'tile', floorTile: '30x30', wall: 'tile', wallTile: '30x60', tileH: 'ceil', ceil: 'none', label: '浴廁' },
    kitchen: { floor: 'tile', floorTile: '60x60', wall: 'tile', wallTile: '30x60', tileH: 'ceil', ceil: 'paint', label: '廚房' },
    balcony: { floor: 'tile', floorTile: '30x30', wall: 'none', wallTile: '', tileH: 0, ceil: 'paint', label: '陽台/露台' },
    public:  { floor: 'tile', floorTile: '60x60', wall: 'paint', wallTile: '', tileH: 0, ceil: 'paint', label: '公共空間' },
    living:  { floor: 'tile', floorTile: '60x60', wall: 'paint', wallTile: '', tileH: 0, ceil: 'paint', label: '居室' },
    service: { floor: 'screed', floorTile: '', wall: 'paint', wallTile: '', tileH: 0, ceil: 'paint', label: '機房/設備' },
  };
}

function defaultParams() {
  return {
    unitToCm: 1,          // 圖面單位換算成 cm
    floorH: 320,          // 樓高 cm
    slabT: 15,            // 版厚 cm
    ceilH: 260,           // 天花板高 cm (油漆/壁磚用)
    beamB: 40, beamD: 70, // 梁寬 / 梁深 cm (含版)
    beamRatio: 0.30,      // 無梁線圖層時 m 梁 / m² 樓地板
    doorH: 210, winH: 150, winSill: 90,
    gapCm: 6,             // 閉合縫隙 (cm)
    repeat: 1,
    extWall: 'tile',      // 外牆: tile / paint / none
    extTile: '4.5x9.5',   // 二丁掛等
    rebar: { slab: 90, beam: 160, column: 200, wall: 100 }, // kg/m³
    brickPerM2: { 12: 64, 24: 128 },
    blockSize: '60x20',   // 白磚(輕質磚) 長x高 cm
    boardSize: '91x182',  // 輕隔間板材 cm
    boardLayers: 1,       // 每面板材層數
    studSpacing: 40,      // 立柱間距 cm
    loss: { concrete: 2, rebar: 3, brick: 5, mortar: 5, tile: 5, paint: 0, form: 0 },
  };
}

/* ------------------------------------------------------------------ */
/* 6. 區域分析                                                          */
/* ------------------------------------------------------------------ */
function segIntersectBox(p, box) { return !(p.bb[2] < box[0] || p.bb[0] > box[2] || p.bb[3] < box[1] || p.bb[1] > box[3]); }

function analyzeRegion(F, box, layerRoles, params, onProgress) {
  // box: [x0,y0,x1,y1] 圖面單位。layerRoles: {layerName:{role,thk}}
  const U = params.unitToCm;
  const roleOf = F.layerNames.map(n => (layerRoles[n] || { role: 'ignore' }));
  const inside = (x, y) => x >= box[0] && x <= box[2] && y >= box[1] && y <= box[3];
  const polys = F.polys.filter(p => segIntersectBox(p, box));
  const W = box[2] - box[0], H = box[3] - box[1];
  // 像素尺寸:最長邊 ~2400px,且不小於 1cm
  let px = Math.max(1 / U, Math.max(W, H) / 2400);
  const nx = Math.ceil(W / px) + 2, ny = Math.ceil(H / px) + 2;
  const N = nx * ny;
  const bar = new Uint8Array(N);
  const X = x => Math.floor((x - box[0]) / px) + 1;
  const Y = y => Math.floor((y - box[1]) / px) + 1;
  function line(x0, y0, x1, y1, M) {
    let ax = X(x0), ay = Y(y0), bx = X(x1), by = Y(y1);
    const dx = Math.abs(bx - ax), dy = Math.abs(by - ay), sx = ax < bx ? 1 : -1, sy = ay < by ? 1 : -1;
    let err = dx - dy, guard = 0;
    while (true) {
      if (ax >= 0 && ay >= 0 && ax < nx && ay < ny) M[ay * nx + ax] = 1;
      if (ax === bx && ay === by) break;
      if (++guard > 20000) break;
      const e2 = 2 * err;
      if (e2 > -dy) { err -= dy; ax += sx; }
      if (e2 < dx) { err += dx; ay += sy; }
    }
  }
  const BARRIER = new Set(['wall_rc', 'wall_brick', 'wall_block', 'wall_light', 'column', 'rail', 'boundary']);
  // 門窗開口(圖塊)
  const openings = detectOpenings(F, polys, roleOf, box, params);
  const opIns = new Set(); for (const o of openings) opIns.add(o.id);
  const inOpening = (p) => { let a = p.ins; while (a >= 0) { if (opIns.has(a)) return true; a = F.inserts[a].parent; } return false; };
  const wallBar = new Uint8Array(N), railBar = new Uint8Array(N);
  for (const p of polys) {
    const r = roleOf[p.L].role;
    const isOp = r === 'door' || r === 'window';
    if (!BARRIER.has(r) && !isOp) continue;
    // 門片、開門弧線也當邊界(防止門洞判斷失誤時漏接),事後再併回房間
    const q = p.p;
    for (let i = 0; i + 3 < q.length; i += 2) { line(q[i], q[i + 1], q[i + 2], q[i + 3], bar); if (r === 'rail') line(q[i], q[i + 1], q[i + 2], q[i + 3], railBar); else if (!isOp) line(q[i], q[i + 1], q[i + 2], q[i + 3], wallBar); }
  }
  const wallNear = (x, y, rad) => { const ix = X(x), iy = Y(y); for (let dy = -rad; dy <= rad; dy++) for (let dx = -rad; dx <= rad; dx++) { const xx = ix + dx, yy = iy + dy; if (xx >= 0 && yy >= 0 && xx < nx && yy < ny && wallBar[yy * nx + xx]) return true; } return false; };
  const nearR = Math.max(2, Math.round(10 / U / px));
  for (const o of openings) {
    const c = o.box;
    if (o.kind === 'window') { for (let i = 0; i < 4; i++) { const a = c[i], b = c[(i + 1) % 4]; line(a[0], a[1], b[0], b[1], bar); line(a[0], a[1], b[0], b[1], wallBar); } continue; }
    // 門:只畫貼牆的那一邊(門洞),門扇擺動範圍算進房間
    let best = -1, bi = -1;
    for (let i = 0; i < 4; i++) {
      const a = c[i], b = c[(i + 1) % 4];
      const L = Math.hypot(b[0] - a[0], b[1] - a[1]);
      const sc = (wallNear(a[0], a[1], nearR) ? 1 : 0) + (wallNear(b[0], b[1], nearR) ? 1 : 0);
      // 門洞那一邊:兩端靠牆、中段沒有牆
      let mid = 0; for (const f of [0.3, 0.5, 0.7]) if (wallNear(a[0] + (b[0] - a[0]) * f, a[1] + (b[1] - a[1]) * f, 1)) mid++;
      const v = L - mid * 1e6;
      if (sc === 2 && mid === 0 && v > best) { best = v; bi = i; }
    }
    if (bi < 0) { for (let i = 0; i < 4; i++) { const a = c[i], b = c[(i + 1) % 4]; line(a[0], a[1], b[0], b[1], bar); } o.chord = null; continue; }
    const a = c[bi], b = c[(bi + 1) % 4];
    line(a[0], a[1], b[0], b[1], bar); line(a[0], a[1], b[0], b[1], wallBar); o.chord = [a, b];
  }
  if (onProgress) onProgress(0.3);
  // 膨脹(閉合縫隙)
  const r = Math.max(1, Math.round(params.gapCm / U / px / 2));
  const wall = dilate(bar, nx, ny, r);
  const wallD = dilate(wallBar, nx, ny, r);
  if (onProgress) onProgress(0.45);
  // 外部
  const lab = new Int32Array(N); // 0 未標, -1 外部, -2 牆, >0 房間
  for (let i = 0; i < N; i++) if (wall[i]) lab[i] = -2;
  floodFill(lab, nx, ny, [0], -1, 0);
  // 房間標籤
  const labels = F.texts.filter(t => inside(t.x, t.y) && isRoomLabel(t.s));
  const rooms = [];
  const footprintCount = (() => { let c = 0; for (let i = 0; i < N; i++) if (lab[i] !== -1) c++; return c; })();
  for (const t of labels) {
    let ix = X(t.x), iy = Y(t.y);
    let seed = findFree(lab, nx, ny, ix, iy, Math.ceil(30 / U / px));
    if (seed < 0) { rooms.push({ name: t.s, type: roomTypeOf(t.s), status: 'noseed', x: t.x, y: t.y }); continue; }
    const v = lab[seed];
    if (v > 0) { const rm = rooms.find(q => q.id === v); if (rm && rm.names.indexOf(t.s) < 0) rm.names.push(t.s); continue; }
    if (v === -1) { rooms.push({ name: t.s, type: roomTypeOf(t.s), status: 'open', x: t.x, y: t.y }); continue; }
    const id = rooms.length + 1;
    let cnt = floodFill(lab, nx, ny, [seed], id, 0, Math.max(footprintCount * 0.6, 10));
    // 標籤落在小封閉區(設備、門框內)時,往周圍找較大的區域
    const minPx = 1.0e4 / ((px * U) * (px * U));
    if (cnt > 0 && cnt < minPx) {
      let done = false;
      for (const dist of [25, 45, 70]) {
        for (let k = 0; k < 16 && !done; k++) {
          const ang = k * Math.PI / 8;
          const sx = X(t.x + Math.cos(ang) * dist / U), sy = Y(t.y + Math.sin(ang) * dist / U);
          if (sx < 0 || sy < 0 || sx >= nx || sy >= ny) continue;
          const si = sy * nx + sx;
          if (lab[si] !== 0) continue;
          const c2 = floodFill(lab, nx, ny, [si], id, 0, Math.max(footprintCount * 0.6, 10));
          if (c2 >= minPx) { cnt += c2; done = true; }
          else { for (let i = 0; i < N; i++) if (lab[i] === id) lab[i] = 0; floodFill(lab, nx, ny, [seed], id, 0); }
        }
        if (done) break;
      }
      if (done) {
        // 小區域併入(設備內部),保留
      }
    }
    if (cnt < 0) { // 溢出:回復
      for (let i = 0; i < N; i++) if (lab[i] === id) lab[i] = 0;
      rooms.push({ id: -id, name: t.s, type: roomTypeOf(t.s), status: 'leak', x: t.x, y: t.y });
      continue;
    }
    rooms.push({ id, name: t.s, names: [t.s], type: roomTypeOf(t.s), status: 'ok', x: t.x, y: t.y, count: cnt });
  }
  // 門扇範圍併回房間:門框內未標示的小區塊 + 門片線條像素
  for (const o of openings) {
    if (o.kind !== 'door') continue;
    const c = o.box;
    const xs = c.map(q => X(q[0])), ys = c.map(q => Y(q[1]));
    const x0 = Math.max(0, Math.min(...xs) - r - 1), x1 = Math.min(nx - 1, Math.max(...xs) + r + 1);
    const y0 = Math.max(0, Math.min(...ys) - r - 1), y1 = Math.min(ny - 1, Math.max(...ys) + r + 1);
    for (let pass = 0; pass < 400; pass++) {
      let changed = 0;
      for (let y = y0; y <= y1; y++) for (let x = x0; x <= x1; x++) {
        const i = y * nx + x;
        const v = lab[i];
        if (!(v === 0 || (v === -2 && !wallD[i]))) continue;
        let best = 0;
        const nb = [x > 0 ? lab[i - 1] : 0, x < nx - 1 ? lab[i + 1] : 0, y > 0 ? lab[i - nx] : 0, y < ny - 1 ? lab[i + nx] : 0];
        for (const q of nb) if (q > 0) { best = q; break; }
        if (best > 0 && rooms.some(rm => rm.id === best && rm.status === 'ok')) { lab[i] = best; changed++; }
      }
      if (!changed) break;
    }
  }
  for (const rm of rooms) if (rm.status === 'ok') { let c = 0; for (let i = 0; i < N; i++) if (lab[i] === rm.id) c++; rm.count = c; }
  if (onProgress) onProgress(0.7);
  // 房間面積/周長
  const cm2 = (px * U) * (px * U);
  const okRooms = rooms.filter(r => r.status === 'ok');
  const edgeCount = new Float64Array(rooms.length + 2);
  for (const rm of okRooms) {
    const loops = traceLoops(lab, nx, ny, rm.id);
    let per = 0; const polysOut = [];
    for (const lp of loops) {
      const simp = dpSimplify(lp, 1.2);
      let L = 0; for (let i = 0; i < simp.length; i++) { const a = simp[i], b = simp[(i + 1) % simp.length]; L += Math.hypot(a[0] - b[0], a[1] - b[1]); }
      per += L;
      polysOut.push(simp.map(q => [box[0] + (q[0] - 1) * px, box[1] + (q[1] - 1) * px]));
    }
    // 修正:膨脹造成的內縮 (r + 0.5 px)
    const off = (r + 0.5) * px * U;
    const perCm = per * px * U;
    rm.area = (rm.count * cm2 + perCm * off) / 1e4;   // m²
    rm.perim = (perCm + 8 * off) / 100;                // m
    rm.outline = polysOut;
  }
  // 建築外框(footprint)
  const fpLoops = traceLoops(lab, nx, ny, -1, true);
  let extPer = 0; const fpOut = [];
  let fpArea = 0;
  for (const lp of fpLoops) {
    const simp = dpSimplify(lp, 1.5);
    let L = 0, A = 0;
    for (let i = 0; i < simp.length; i++) { const a = simp[i], b = simp[(i + 1) % simp.length]; L += Math.hypot(a[0] - b[0], a[1] - b[1]); A += a[0] * b[1] - b[0] * a[1]; }
    // 只取大圈(建築外圍),忽略微小殘留
    if (Math.abs(A) / 2 * cm2 < 4e4) continue; // < 4 m²
    extPer += L; fpArea += Math.abs(A) / 2;
    fpOut.push(simp.map(q => [box[0] + (q[0] - 1) * px, box[1] + (q[1] - 1) * px]));
  }
  // 外框為「外部」區域的邊界,外部區域邊界包含整個框邊——剔除與框邊重合者
  // traceLoops(-1, true) 只回傳外部與非外部的交界,不含畫布外緣。
  const offE = (r + 0.5) * px * U;
  // 外圍中屬於欄杆的比例
  let wCnt = 0, rCnt = 0; const rr = r + 3;
  for (let y = 1; y < ny - 1; y += 2) for (let x = 1; x < nx - 1; x += 2) {
    const i = y * nx + x; if (lab[i] !== -1) continue;
    if (lab[i - 1] === -1 && lab[i + 1] === -1 && lab[i - nx] === -1 && lab[i + nx] === -1) continue;
    let hw = false, hr = false;
    for (let dy = -rr; dy <= rr && !hw; dy++) for (let dx = -rr; dx <= rr; dx++) { const xx = x + dx, yy = y + dy; if (xx < 0 || yy < 0 || xx >= nx || yy >= ny) continue; const j = yy * nx + xx; if (wallBar[j]) { hw = true; break; } if (railBar[j]) hr = true; }
    if (hw) wCnt++; else if (hr) rCnt++;
  }
  const railFrac = wCnt + rCnt ? rCnt / (wCnt + rCnt) : 0;
  const footprint = { railFrac, area: (fpArea * cm2 - extPer * px * U * offE) / 1e4, perim: Math.max(0, extPer * px * U - 8 * offE) / 100, outline: fpOut };

  // 牆長
  const walls = wallLengths(polys, roleOf, U);
  // 柱
  const columns = detectColumns(F, polys, roleOf, U);
  // 梁
  let beamLen = 0; let beamFromLayer = false;
  for (const p of polys) if (roleOf[p.L].role === 'beam') { const q = p.p; for (let i = 0; i + 3 < q.length; i += 2) beamLen += Math.hypot(q[i + 2] - q[i], q[i + 3] - q[i + 1]); }
  if (beamLen > 0) { beamFromLayer = true; beamLen = beamLen * U / 2 / 100; }
  // 開口分配到牆種、房間、外部
  assignOpenings(openings, polys, roleOf, lab, nx, ny, px, box, U, rooms);
  if (onProgress) onProgress(1);
  return { box, px, nx, ny, lab, rooms, footprint, walls, columns, beamLen, beamFromLayer, openings, labelsFound: labels.length };
}

function dilate(src, nx, ny, r) {
  // 方形結構元素,兩次一維掃描
  const tmp = new Uint8Array(src.length), out = new Uint8Array(src.length);
  for (let y = 0; y < ny; y++) {
    let last = -1e9; const row = y * nx;
    for (let x = 0; x < nx; x++) { if (src[row + x]) last = x; if (x - last <= r) tmp[row + x] = 1; }
    last = 1e9;
    for (let x = nx - 1; x >= 0; x--) { if (src[row + x]) last = x; if (last - x <= r) tmp[row + x] = 1; }
  }
  for (let x = 0; x < nx; x++) {
    let last = -1e9;
    for (let y = 0; y < ny; y++) { if (tmp[y * nx + x]) last = y; if (y - last <= r) out[y * nx + x] = 1; }
    last = 1e9;
    for (let y = ny - 1; y >= 0; y--) { if (tmp[y * nx + x]) last = y; if (last - y <= r) out[y * nx + x] = 1; }
  }
  return out;
}

function floodFill(lab, nx, ny, seeds, val, target, maxCount) {
  const stack = new Int32Array(Math.max(1024, nx * ny >> 2));
  let sp = 0, cnt = 0;
  let st = stack;
  for (const s of seeds) if (lab[s] === target) { lab[s] = val; st[sp++] = s; }
  while (sp > 0) {
    const i = st[--sp]; cnt++;
    if (maxCount && cnt > maxCount) return -1;
    const x = i % nx;
    const nb = [x > 0 ? i - 1 : -1, x < nx - 1 ? i + 1 : -1, i >= nx ? i - nx : -1, i + nx < nx * ny ? i + nx : -1];
    for (const j of nb) {
      if (j >= 0 && lab[j] === target) {
        lab[j] = val;
        if (sp >= st.length) { const ns = new Int32Array(st.length * 2); ns.set(st); st = ns; }
        st[sp++] = j;
      }
    }
  }
  // 邊界上的種子:外部填滿要從四周開始
  return cnt;
}

function findFree(lab, nx, ny, ix, iy, rad) {
  for (let d = 0; d <= rad; d++) {
    for (let dy = -d; dy <= d; dy++) for (let dx = -d; dx <= d; dx++) {
      if (Math.max(Math.abs(dx), Math.abs(dy)) !== d) continue;
      const x = ix + dx, y = iy + dy;
      if (x < 0 || y < 0 || x >= nx || y >= ny) continue;
      const v = lab[y * nx + x];
      if (v !== -2) return y * nx + x;
    }
  }
  return -1;
}

/* 追蹤 label===id 區域的邊界(像素角點座標),回傳多個封閉迴圈 */
function traceLoops(lab, nx, ny, id, outsideMode) {
  // outsideMode: 追蹤 外部(-1) 與 非外部 的交界(只取 footprint 邊界)
  const isIn = outsideMode ? (i => lab[i] !== -1) : (i => lab[i] === id);
  // 有向邊:區域在左側。以頂點 (x,y) 為 key。
  const next = new Map();
  const key = (x, y) => y * (nx + 1) + x;
  for (let y = 0; y < ny; y++) for (let x = 0; x < nx; x++) {
    const i = y * nx + x;
    if (!isIn(i)) continue;
    // 下邊 (y) : 若下方不在區域 -> 邊 (x,y)->(x+1,y)
    if (y === 0 || !isIn(i - nx)) addE(next, key(x, y), key(x + 1, y));
    if (x === nx - 1 || !isIn(i + 1)) addE(next, key(x + 1, y), key(x + 1, y + 1));
    if (y === ny - 1 || !isIn(i + nx)) addE(next, key(x + 1, y + 1), key(x, y + 1));
    if (x === 0 || !isIn(i - 1)) addE(next, key(x, y + 1), key(x, y));
  }
  function addE(m, a, b) { if (m.has(a)) { const v = m.get(a); if (Array.isArray(v)) v.push(b); else m.set(a, [v, b]); } else m.set(a, b); }
  const loops = [];
  const W1 = nx + 1;
  while (next.size) {
    const startK = next.keys().next().value;
    let k = startK; const lp = [];
    let guard = 0;
    while (true) {
      let v = next.get(k);
      if (v === undefined) break;
      let nk;
      if (Array.isArray(v)) { nk = v.pop(); if (v.length === 1) next.set(k, v[0]); else if (v.length === 0) next.delete(k); }
      else { nk = v; next.delete(k); }
      lp.push([k % W1, Math.floor(k / W1)]);
      k = nk;
      if (k === startK || ++guard > 5e6) break;
    }
    if (lp.length >= 4) loops.push(lp);
  }
  return loops;
}

function dpSimplify(pts, eps) {
  // 先去掉共線點
  const P = [];
  for (let i = 0; i < pts.length; i++) {
    const a = pts[(i - 1 + pts.length) % pts.length], b = pts[i], c = pts[(i + 1) % pts.length];
    if ((b[0] - a[0]) * (c[1] - b[1]) - (b[1] - a[1]) * (c[0] - b[0]) !== 0) P.push(b);
  }
  if (P.length < 4) return P.length ? P : pts;
  // 封閉 DP:從最遠兩點切開
  let i0 = 0, i1 = 0, best = -1;
  for (let i = 0; i < P.length; i++) { const d = (P[i][0] - P[0][0]) ** 2 + (P[i][1] - P[0][1]) ** 2; if (d > best) { best = d; i1 = i; } }
  const A = P.slice(i0, i1 + 1), B = P.slice(i1).concat([P[0]]);
  const sa = dp(A, eps), sb = dp(B, eps);
  return sa.slice(0, -1).concat(sb.slice(0, -1));
}
function dp(pts, eps) {
  if (pts.length < 3) return pts;
  const keep = new Uint8Array(pts.length); keep[0] = keep[pts.length - 1] = 1;
  const st = [[0, pts.length - 1]];
  while (st.length) {
    const [s, e] = st.pop();
    const ax = pts[s][0], ay = pts[s][1], bx = pts[e][0], by = pts[e][1];
    const L = Math.hypot(bx - ax, by - ay) || 1;
    let md = -1, mi = -1;
    for (let i = s + 1; i < e; i++) { const d = Math.abs((bx - ax) * (ay - pts[i][1]) - (ax - pts[i][0]) * (by - ay)) / L; if (d > md) { md = d; mi = i; } }
    if (md > eps) { keep[mi] = 1; st.push([s, mi], [mi, e]); }
  }
  return pts.filter((_, i) => keep[i]);
}

/* 牆長:各牆圖層線段總長 / 2(兩面線),去除牆頭短線 */
// 牆長:只算「有另一條平行線、間距約等於牆厚」的那一段(兩面牆線重疊的部分),再除以 2。
// 這樣管道間小格子、符號、凸窗鋸齒線、重複畫的線都不會被當成牆。
function wallLengths(polys, roleOf, U) {
  const res = {}, segsOf = {};
  for (const p of polys) {
    const ro = roleOf[p.L];
    if (!ro.role.startsWith('wall_')) continue;
    const thk = ro.thk || 15;
    const key = ro.role + '|' + thk;
    if (!res[key]) { res[key] = { role: ro.role, thk, len: 0, raw: 0, layers: new Set() }; segsOf[key] = { segs: [], seen: new Set() }; }
    res[key].layers.add(p.L);
    const q = p.p, S = segsOf[key];
    for (let i = 0; i + 3 < q.length; i += 2) {
      const x0 = q[i] * U, y0 = q[i + 1] * U, x1 = q[i + 2] * U, y1 = q[i + 3] * U; // cm
      const l = Math.hypot(x1 - x0, y1 - y0);
      res[key].raw += l;
      if (l < 1) continue;
      const k1 = Math.round(x0) + ',' + Math.round(y0) + ',' + Math.round(x1) + ',' + Math.round(y1);
      const k2 = Math.round(x1) + ',' + Math.round(y1) + ',' + Math.round(x0) + ',' + Math.round(y0);
      if (S.seen.has(k1) || S.seen.has(k2)) continue; // 重複畫的線
      S.seen.add(k1);
      S.segs.push([x0, y0, x1, y1, l, Math.min(x0, x1), Math.min(y0, y1), Math.max(x0, x1), Math.max(y0, y1)]);
    }
  }
  for (const k in res) {
    const thk = res[k].thk, segs = segsOf[k].segs, dMin = thk * 0.7, dMax = thk * 1.3;
    segs.sort((a, b) => a[5] - b[5]);
    let tot = 0;
    for (let ai = 0; ai < segs.length; ai++) {
      const a = segs[ai], L = a[4];
      if (L <= thk * 1.3) continue; // 牆頭
      const ux = (a[2] - a[0]) / L, uy = (a[3] - a[1]) / L, iv = [];
      for (let ci = 0; ci < segs.length; ci++) {
        const c = segs[ci];
        if (c[5] > a[7] + dMax) break;
        if (ci === ai || c[7] < a[5] - dMax || c[6] > a[8] + dMax || c[8] < a[6] - dMax) continue;
        const cx = c[2] - c[0], cy = c[3] - c[1];
        if (Math.abs(ux * cy - uy * cx) / c[4] > 0.03) continue; // 不平行
        const d = Math.abs((c[0] - a[0]) * uy - (c[1] - a[1]) * ux);
        if (d < dMin || d > dMax) continue;
        let t0 = (c[0] - a[0]) * ux + (c[1] - a[1]) * uy, t1 = (c[2] - a[0]) * ux + (c[3] - a[1]) * uy;
        if (t0 > t1) { const tt = t0; t0 = t1; t1 = tt; }
        t0 = Math.max(0, t0); t1 = Math.min(L, t1);
        if (t1 > t0) iv.push([t0, t1]);
      }
      iv.sort((x, y) => x[0] - y[0]);
      let e = -1;
      for (const [s, t] of iv) { if (t <= e) continue; tot += t - Math.max(s, e); e = t; }
    }
    res[k].len = tot / 2 / 100; res[k].layers = [...res[k].layers];
  }
  return Object.values(res);
}

function polyArea(q) { let A = 0; for (let i = 0; i + 3 < q.length; i += 2) A += q[i] * q[i + 3] - q[i + 2] * q[i + 1]; const n = q.length; if (q[0] !== q[n - 2] || q[1] !== q[n - 1]) A += q[n - 2] * q[1] - q[0] * q[n - 1]; return Math.abs(A) / 2; }

function detectColumns(F, polys, roleOf, U) {
  // 柱:柱圖層上的封閉多邊形(去除重複),或柱圖層上的圖塊外框
  const cands = [];
  for (const p of polys) {
    if (roleOf[p.L].role !== 'column') continue;
    const q = p.p; const n = q.length;
    const closed = p.c || (n >= 8 && Math.hypot(q[0] - q[n - 2], q[1] - q[n - 1]) < 1e-6);
    if (!closed) continue;
    const A = polyArea(q) * U * U;
    if (A < 400 || A > 40000) continue; // 20x20 ~ 200x200 cm
    const w = (p.bb[2] - p.bb[0]) * U, h = (p.bb[3] - p.bb[1]) * U;
    cands.push({ cx: (p.bb[0] + p.bb[2]) / 2, cy: (p.bb[1] + p.bb[3]) / 2, A, P: perim(q) * U, w, h });
  }
  // 以中心點去重(取最大)
  cands.sort((a, b) => b.A - a.A);
  const out = [];
  for (const c of cands) {
    if (out.some(o => Math.hypot(o.cx - c.cx, o.cy - c.cy) * U < 15 || (Math.abs(o.cx - c.cx) * U < o.w / 2 && Math.abs(o.cy - c.cy) * U < o.h / 2))) continue;
    out.push(c);
  }
  return out;
}
function perim(q) { let L = 0; for (let i = 0; i + 3 < q.length; i += 2) L += Math.hypot(q[i + 2] - q[i], q[i + 3] - q[i + 1]); return L; }

/* 門窗:以「最內層圖塊」中大部分線條屬於 門/窗 圖層者為開口 */
function detectOpenings(F, polys, roleOf, box, params) {
  const U = params.unitToCm;
  const acc = new Map(); // insId -> {door, window, total}
  for (const p of polys) {
    if (p.ins < 0) continue;
    const r = roleOf[p.L].role;
    let a = acc.get(p.ins); if (!a) { a = { door: 0, window: 0, total: 0 }; acc.set(p.ins, a); }
    const l = perim(p.p);
    a.total += l; if (r === 'door') a.door += l; else if (r === 'window') a.window += l;
  }
  // 圖塊本身所在圖層也算
  const res = [];
  const used = new Set();
  // 從內往外:深度大的優先
  const ids = [...acc.keys()].sort((a, b) => F.inserts[b].depth - F.inserts[a].depth);
  for (const id of ids) {
    const ins = F.inserts[id];
    if (!ins.box) continue;
    const a = acc.get(id);
    let kind = null;
    const ir = roleOf[ins.L].role;
    if (a.door > 0.5 * a.total || (ir === 'door' && a.door + a.window < 0.5 * a.total && a.total > 0 && a.door >= a.window)) kind = 'door';
    if (a.window > 0.5 * a.total || (ir === 'window' && a.window >= a.door && a.total > 0 && !kind)) kind = 'window';
    if (!kind) continue;
    const w = Math.max(ins.w, ins.h) * U, d = Math.min(ins.w, ins.h) * U;
    if (w < 40 || w > 600) continue;
    // 祖先已列入者不重複
    let anc = ins.parent, skip = false;
    while (anc >= 0) { if (used.has(anc)) { skip = true; break; } anc = F.inserts[anc].parent; }
    if (skip) continue;
    // 子孫已列入者:本圖塊為外層,跳過
    const cx = (ins.box[0][0] + ins.box[2][0]) / 2, cy = (ins.box[0][1] + ins.box[2][1]) / 2;
    if (cx < box[0] || cx > box[2] || cy < box[1] || cy > box[3]) continue;
    if (res.some(o => Math.hypot(o.cx - cx, o.cy - cy) * U < 10)) continue;
    used.add(id);
    // 門寬:門片圖塊的外框為 w x w (含開門弧),寬度取長邊
    res.push({ kind, w, d, cx, cy, box: ins.box, name: ins.name, id });
  }
  return res;
}

function assignOpenings(openings, polys, roleOf, lab, nx, ny, px, box, U, rooms) {
  // 牆線格網索引
  const cell = 100 / U;
  const grid = new Map();
  for (const p of polys) {
    const ro = roleOf[p.L]; if (!ro.role.startsWith('wall_')) continue;
    const q = p.p;
    for (let i = 0; i + 3 < q.length; i += 2) {
      const gx0 = Math.floor(Math.min(q[i], q[i + 2]) / cell), gx1 = Math.floor(Math.max(q[i], q[i + 2]) / cell);
      const gy0 = Math.floor(Math.min(q[i + 1], q[i + 3]) / cell), gy1 = Math.floor(Math.max(q[i + 1], q[i + 3]) / cell);
      if ((gx1 - gx0 + 1) * (gy1 - gy0 + 1) > 400) continue;
      for (let gx = gx0; gx <= gx1; gx++) for (let gy = gy0; gy <= gy1; gy++) { const k = gx + ',' + gy; if (!grid.has(k)) grid.set(k, []); grid.get(k).push([q[i], q[i + 1], q[i + 2], q[i + 3], ro]); }
    }
  }
  const roomById = new Map(rooms.filter(r => r.status === 'ok').map(r => [r.id, r]));
  for (const o of openings) {
    // 最近牆線
    let best = Infinity, bro = null;
    const gx = Math.floor(o.cx / cell), gy = Math.floor(o.cy / cell);
    // 以開口兩端點為準(門寬方向)
    const c = o.box;
    const e1 = Math.hypot(c[1][0] - c[0][0], c[1][1] - c[0][1]), e2 = Math.hypot(c[3][0] - c[0][0], c[3][1] - c[0][1]);
    const pts = [[o.cx, o.cy], ...c];
    for (let dx = -1; dx <= 1; dx++) for (let dy = -1; dy <= 1; dy++) {
      const arr = grid.get((gx + dx) + ',' + (gy + dy)); if (!arr) continue;
      for (const s of arr) for (const p of pts) { const d = pointSeg(p[0], p[1], s); if (d < best) { best = d; bro = s[4]; } }
    }
    o.wall = bro && best * U < 80 ? bro : null;
    // 相鄰房間 / 外部:取開口外框外擴一圈的像素
    const ids = new Map(); let outside = 0;
    const minx = Math.min(...c.map(q => q[0])), maxx = Math.max(...c.map(q => q[0])), miny = Math.min(...c.map(q => q[1])), maxy = Math.max(...c.map(q => q[1]));
    const pad = 40 / U;
    const step = Math.max(px, 5 / U);
    for (let x = minx - pad; x <= maxx + pad; x += step) for (let y = miny - pad; y <= maxy + pad; y += step) {
      if (x > minx && x < maxx && y > miny && y < maxy) continue;
      const ix = Math.floor((x - box[0]) / px) + 1, iy = Math.floor((y - box[1]) / px) + 1;
      if (ix < 0 || iy < 0 || ix >= nx || iy >= ny) continue;
      const v = lab[iy * nx + ix];
      if (v > 0) ids.set(v, (ids.get(v) || 0) + 1); else if (v === -1) outside++;
    }
    const sorted = [...ids.entries()].sort((a, b) => b[1] - a[1]);
    o.rooms = sorted.slice(0, 2).map(e => e[0]).filter(id => roomById.has(id));
    o.exterior = outside > 2 && o.rooms.length <= 1;
  }
}
function pointSeg(px, py, s) { const [ax, ay, bx, by] = s; const dx = bx - ax, dy = by - ay; const L2 = dx * dx + dy * dy || 1; let t = ((px - ax) * dx + (py - ay) * dy) / L2; t = Math.max(0, Math.min(1, t)); return Math.hypot(ax + t * dx - px, ay + t * dy - py); }

/* ------------------------------------------------------------------ */
/* 7. 數量計算                                                          */
/* ------------------------------------------------------------------ */
function tileArea(spec) { const m = /([\d.]+)\s*[x×*]\s*([\d.]+)/i.exec(spec || ''); return m ? parseFloat(m[1]) * parseFloat(m[2]) / 1e4 : 0; }

function computeQuantities(A, params, finishes, roomOverrides) {
  const P = params;
  const H = P.floorH / 100, t = P.slabT / 100, Hc = P.ceilH / 100;
  const Hw = H - t; // 牆淨高(至版底)
  const items = []; // {trade, item, unit, qty, lossKey, note}
  const add = (trade, item, unit, qty, lossKey, note) => { if (qty > 1e-6) items.push({ trade, item, unit, qty, lossKey, note: note || '' }); };
  const ov = roomOverrides || {};
  const rooms = A.rooms.filter(r => r.status === 'ok' && !(ov[r.id] && ov[r.id].exclude)).map(r => ({ ...r, type: (ov[r.id] && ov[r.id].type) || mergedType(r) }));
  const floorArea = A.footprint.area;
  // ---- 結構 ----
  const slabV = floorArea * t;
  let beamL = A.beamFromLayer ? A.beamLen : floorArea * P.beamRatio;
  const bB = P.beamB / 100, bD = P.beamD / 100;
  const beamV = beamL * bB * Math.max(0, bD - t);
  let colA = 0, colP = 0; for (const c of A.columns) { colA += c.A / 1e4; colP += c.P / 100; }
  const colV = colA * Hw;
  // 牆 (含開口上下方補回)
  const wallInfo = A.walls.map(w => ({ ...w, area: w.len * Hw }));
  for (const o of A.openings) {
    if (!o.wall) continue;
    const wi = wallInfo.find(w => w.role === o.wall.role && w.thk === (o.wall.thk || 15));
    if (!wi) continue;
    const h = o.kind === 'door' ? P.doorH / 100 : P.winH / 100;
    wi.area += (o.w / 100) * Math.max(0, Hw - h);
  }
  let rcWallV = 0, rcWallA = 0;
  for (const w of wallInfo) if (w.role === 'wall_rc') { rcWallV += w.area * w.thk / 100; rcWallA += w.area; }
  add('結構', '混凝土 — 樓板', 'm³', slabV, 'concrete', `樓地板 ${floorArea.toFixed(2)} m² × 版厚 ${P.slabT} cm`);
  add('結構', '混凝土 — 梁', 'm³', beamV, 'concrete', `${A.beamFromLayer ? '梁線' : '估算'} ${beamL.toFixed(1)} m × ${P.beamB}×(${P.beamD}-${P.slabT}) cm`);
  add('結構', '混凝土 — 柱', 'm³', colV, 'concrete', `${A.columns.length} 支,斷面合計 ${colA.toFixed(2)} m² × ${Hw.toFixed(2)} m`);
  add('結構', '混凝土 — RC牆', 'm³', rcWallV, 'concrete', wallInfo.filter(w => w.role === 'wall_rc').map(w => `${w.thk}cm 牆長 ${w.len.toFixed(1)} m`).join(','));
  const concTotal = slabV + beamV + colV + rcWallV;
  add('結構', '混凝土 — 小計', 'm³', concTotal, 'concrete', '');
  const formSlab = floorArea, formBeam = beamL * (bB + 2 * Math.max(0, bD - t)), formCol = colP * Hw, formWall = rcWallA * 2;
  add('結構', '模板 — 樓板底', 'm²', formSlab, 'form');
  add('結構', '模板 — 梁', 'm²', formBeam, 'form', '梁底 + 兩側');
  add('結構', '模板 — 柱', 'm²', formCol, 'form', `柱周長合計 ${colP.toFixed(1)} m`);
  add('結構', '模板 — RC牆', 'm²', formWall, 'form', '雙面');
  add('結構', '模板 — 小計', 'm²', formSlab + formBeam + formCol + formWall, 'form');
  const rb = P.rebar;
  const steel = (slabV * rb.slab + beamV * rb.beam + colV * rb.column + rcWallV * rb.wall) / 1000;
  add('結構', '鋼筋', 't', steel, 'rebar', `依含筋率 版${rb.slab}/梁${rb.beam}/柱${rb.column}/牆${rb.wall} kg/m³`);
  // ---- 泥作 ----
  for (const w of wallInfo) if (w.role === 'wall_brick') {
    const per = P.brickPerM2[w.thk] || (w.thk >= 20 ? 128 : 64);
    add('泥作', `砌磚牆 ${w.thk >= 20 ? '1B' : '1/2B'} (${w.thk}cm)`, 'm²', w.area, 'brick', `牆長 ${w.len.toFixed(1)} m × ${Hw.toFixed(2)} m`);
    add('泥作', `紅磚 ${w.thk >= 20 ? '1B' : '1/2B'}`, '塊', w.area * per, 'brick', `${per} 塊/m²`);
  }
  let dryFace = 0;
  for (const w of wallInfo) if (w.role === 'wall_block') {
    const bs = tileArea(P.blockSize || '60x20') || 0.12;
    add('泥作', `白磚/輕質磚牆 (${w.thk}cm)`, 'm²', w.area, 'brick', `牆長 ${w.len.toFixed(1)} m × ${Hw.toFixed(2)} m`);
    add('泥作', `白磚 ${P.blockSize || '60x20'}×${w.thk} cm`, '塊', w.area / bs, 'brick', `${(1 / bs).toFixed(1)} 塊/m²`);
    add('泥作', '白磚黏著劑', 'kg', w.area * 4, 'brick', '約 4 kg/m²');
    dryFace += w.area * 2;
  }
  for (const w of wallInfo) if (w.role === 'wall_light') {
    const ba = tileArea(P.boardSize || '91x182') || 1.656;
    const layers = P.boardLayers || 1;
    add('泥作', `輕隔間牆 (${w.thk}cm)`, 'm²', w.area, 'brick', `牆長 ${w.len.toFixed(1)} m × ${Hw.toFixed(2)} m`);
    add('泥作', `輕隔間板材 ${P.boardSize || '91x182'} cm`, '張', w.area * 2 * layers / ba, 'brick', `雙面 × ${layers} 層`);
    add('泥作', '輕隔間 C 型立柱', 'm', w.len * Hw / ((P.studSpacing || 40) / 100), 'brick', `間距 ${P.studSpacing || 40} cm`);
    add('泥作', '輕隔間 隔音岩棉', 'm²', w.area, 'brick');
    dryFace += w.area * 2;
  }
  // 房間牆面 / 地坪 / 天花
  let paintWall = 0, paintCeil = 0, tileFloor = {}, tileWall = {}, screedFloor = 0, plasterWall = 0, baseWall = 0, baseFloor = 0, woodFloor = 0;
  const roomDetail = [];
  for (const rm of rooms) {
    const f = Object.assign({}, finishes[rm.type] || finishes.living, (ov[rm.id] && ov[rm.id].finish) || {});
    const ops = A.openings.filter(o => o.rooms && o.rooms.indexOf(rm.id) >= 0);
    const Ht = f.wall === 'tile' ? (f.tileH === 'ceil' ? Hc : (parseFloat(f.tileH) || 0) / 100) : 0;
    const dedTo = (top) => { let s = 0; for (const o of ops) { const b = o.kind === 'door' ? 0 : P.winSill / 100; const h = o.kind === 'door' ? P.doorH / 100 : P.winH / 100; s += (o.w / 100) * Math.max(0, Math.min(top, b + h) - Math.min(top, b)); } return s; };
    const wallGrossC = rm.perim * Hc;
    let wTile = 0, wPaint = 0;
    if (f.wall === 'tile') { wTile = Math.max(0, rm.perim * Ht - dedTo(Ht)); wPaint = Math.max(0, rm.perim * (Hc - Ht) - (dedTo(Hc) - dedTo(Ht))); }
    else if (f.wall === 'paint') wPaint = Math.max(0, wallGrossC - dedTo(Hc));
    const plaster = Math.max(0, rm.perim * Hw - dedTo(Hw));
    if (f.wall !== 'none') { plasterWall += Math.max(0, plaster - wTile); baseWall += wTile; }
    paintWall += wPaint;
    if (wTile > 0) tileWall[f.wallTile] = (tileWall[f.wallTile] || 0) + wTile;
    if (f.floor === 'tile') { tileFloor[f.floorTile] = (tileFloor[f.floorTile] || 0) + rm.area; baseFloor += rm.area; }
    else if (f.floor === 'wood') { woodFloor += rm.area; screedFloor += rm.area; }
    else if (f.floor === 'screed') screedFloor += rm.area;
    if (f.ceil === 'paint') paintCeil += rm.area;
    roomDetail.push({ id: rm.id, name: rm.name, type: rm.type, area: rm.area, perim: rm.perim, wallTile: wTile, wallPaint: wPaint, ceilPaint: f.ceil === 'paint' ? rm.area : 0, floor: f.floor === 'tile' ? f.floorTile + ' 磁磚' : f.floor === 'wood' ? '木地板' : f.floor === 'screed' ? '粉光' : '—', openings: ops.length });
  }
  // 外牆
  const extOps = A.openings.filter(o => o.exterior);
  let extOpenA = 0; for (const o of extOps) extOpenA += (o.w / 100) * (o.kind === 'door' ? P.doorH / 100 : P.winH / 100);
  const railF = A.footprint.railFrac || 0;
  const extWallLen = A.footprint.perim * (1 - railF);
  const extWallA = Math.max(0, extWallLen * H - extOpenA);
  if (railF > 0) add('其他', '陽台欄杆/矮牆(外圍)', 'm', A.footprint.perim * railF, 'form', '外圍周長中屬欄杆部分');
  add('泥作', '外牆 1:3 水泥砂漿打底', 'm²', extWallA, 'mortar', `外牆長 ${extWallLen.toFixed(1)} m × 樓高 ${H} m − 外牆開口 ${extOpenA.toFixed(1)} m²`);
  // 白磚、輕隔間牆面不做水泥粉刷,改為批土
  const skim = Math.min(dryFace, plasterWall);
  plasterWall -= skim;
  add('泥作', '內牆 1:3 水泥砂漿粉刷(油漆面)', 'm²', plasterWall, 'mortar', '至版底,扣門窗' + (skim ? `;已扣白磚/輕隔間面 ${skim.toFixed(1)} m²` : ''));
  add('泥作', '內牆 1:3 水泥砂漿打底(貼磚面)', 'm²', baseWall, 'mortar');
  add('泥作', '地坪 1:3 水泥砂漿打底(貼磚)', 'm²', baseFloor, 'mortar');
  add('泥作', '地坪 水泥砂漿粉光', 'm²', screedFloor, 'mortar', woodFloor ? `含木地板區 ${woodFloor.toFixed(1)} m²` : '');
  // ---- 磁磚 ----
  for (const k in tileFloor) { add('磁磚', `地磚 ${k} cm`, 'm²', tileFloor[k], 'tile'); const ta = tileArea(k); if (ta) add('磁磚', `地磚 ${k} cm 片數`, '片', tileFloor[k] / ta, 'tile'); }
  for (const k in tileWall) { add('磁磚', `壁磚 ${k} cm`, 'm²', tileWall[k], 'tile'); const ta = tileArea(k); if (ta) add('磁磚', `壁磚 ${k} cm 片數`, '片', tileWall[k] / ta, 'tile'); }
  if (P.extWall === 'tile') add('磁磚', `外牆磚 ${P.extTile} cm`, 'm²', extWallA, 'tile');
  // ---- 油漆 ----
  if (skim) add('油漆', '批土整平(白磚/輕隔間面)', 'm²', skim, 'paint', '取代水泥粉刷');
  add('油漆', '內牆 水泥漆/乳膠漆', 'm²', paintWall, 'paint', '至天花板高,扣門窗');
  add('油漆', '天花板 平頂漆', 'm²', paintCeil, 'paint');
  if (P.extWall === 'paint') add('油漆', '外牆 塗料', 'm²', extWallA, 'paint');
  if (woodFloor) add('其他', '木地板', 'm²', woodFloor, 'tile');
  // 依工種排序
  const TO = ['結構', '泥作', '磁磚', '油漆', '其他'];
  items.sort((a, b) => TO.indexOf(a.trade) - TO.indexOf(b.trade));
  // 損耗
  for (const it of items) { const l = P.loss[it.lossKey] || 0; it.loss = l; it.total = it.qty * (1 + l / 100); }
  return { items, roomDetail, summary: { floorArea, extPerim: A.footprint.perim, rooms: rooms.length, openings: A.openings.length, columns: A.columns.length } };
}

/* ------------------------------------------------------------------ */
/* 8. 簡易 XLSX 產生器 (無外部函式庫)                                    */
/* ------------------------------------------------------------------ */
const CRC_T = (() => { const t = new Uint32Array(256); for (let n = 0; n < 256; n++) { let c = n; for (let k = 0; k < 8; k++) c = c & 1 ? 0xEDB88320 ^ (c >>> 1) : c >>> 1; t[n] = c >>> 0; } return t; })();
function crc32(b) { let c = 0xFFFFFFFF; for (let i = 0; i < b.length; i++) c = CRC_T[(c ^ b[i]) & 0xFF] ^ (c >>> 8); return (c ^ 0xFFFFFFFF) >>> 0; }
function zipStore(files) {
  const enc = new TextEncoder();
  const parts = [], central = [];
  let off = 0;
  for (const f of files) {
    const name = enc.encode(f.name), data = typeof f.data === 'string' ? enc.encode(f.data) : f.data;
    const crc = crc32(data);
    const h = new DataView(new ArrayBuffer(30));
    h.setUint32(0, 0x04034b50, true); h.setUint16(4, 20, true); h.setUint16(6, 0x0800, true); h.setUint16(8, 0, true);
    h.setUint16(10, 0, true); h.setUint16(12, 0x21, true); h.setUint32(14, crc, true); h.setUint32(18, data.length, true); h.setUint32(22, data.length, true);
    h.setUint16(26, name.length, true); h.setUint16(28, 0, true);
    parts.push(new Uint8Array(h.buffer), name, data);
    const c = new DataView(new ArrayBuffer(46));
    c.setUint32(0, 0x02014b50, true); c.setUint16(4, 20, true); c.setUint16(6, 20, true); c.setUint16(8, 0x0800, true); c.setUint16(10, 0, true);
    c.setUint16(12, 0, true); c.setUint16(14, 0x21, true); c.setUint32(16, crc, true); c.setUint32(20, data.length, true); c.setUint32(24, data.length, true);
    c.setUint16(28, name.length, true); c.setUint32(42, off, true);
    central.push(new Uint8Array(c.buffer), name);
    off += 30 + name.length + data.length;
  }
  let csz = 0; for (const c of central) csz += c.length;
  const e = new DataView(new ArrayBuffer(22));
  e.setUint32(0, 0x06054b50, true); e.setUint16(8, files.length, true); e.setUint16(10, files.length, true); e.setUint32(12, csz, true); e.setUint32(16, off, true);
  const all = [...parts, ...central, new Uint8Array(e.buffer)];
  let n = 0; for (const a of all) n += a.length;
  const out = new Uint8Array(n); let p = 0; for (const a of all) { out.set(a, p); p += a.length; }
  return out;
}
function xmlEsc(s) { return String(s).replace(/&/g, '&amp;').replace(/</g, '&lt;').replace(/>/g, '&gt;').replace(/"/g, '&quot;').replace(/[\u0000-\u0008\u000B\u000C\u000E-\u001F]/g, ''); }
function colName(i) { let s = ''; i++; while (i > 0) { const m = (i - 1) % 26; s = String.fromCharCode(65 + m) + s; i = Math.floor((i - 1) / 26); } return s; }
/* sheets: [{name, rows:[[cell,...]], widths:[...], header:true}] cell: string|number|{v, s:styleIdx} */
function buildXLSX(sheets) {
  const files = [];
  files.push({ name: '[Content_Types].xml', data: '<?xml version="1.0" encoding="UTF-8" standalone="yes"?><Types xmlns="http://schemas.openxmlformats.org/package/2006/content-types"><Default Extension="rels" ContentType="application/vnd.openxmlformats-package.relationships+xml"/><Default Extension="xml" ContentType="application/xml"/><Override PartName="/xl/workbook.xml" ContentType="application/vnd.openxmlformats-officedocument.spreadsheetml.sheet.main+xml"/><Override PartName="/xl/styles.xml" ContentType="application/vnd.openxmlformats-officedocument.spreadsheetml.styles+xml"/>' + sheets.map((s, i) => `<Override PartName="/xl/worksheets/sheet${i + 1}.xml" ContentType="application/vnd.openxmlformats-officedocument.spreadsheetml.worksheet+xml"/>`).join('') + '</Types>' });
  files.push({ name: '_rels/.rels', data: '<?xml version="1.0" encoding="UTF-8" standalone="yes"?><Relationships xmlns="http://schemas.openxmlformats.org/package/2006/relationships"><Relationship Id="rId1" Type="http://schemas.openxmlformats.org/officeDocument/2006/relationships/officeDocument" Target="xl/workbook.xml"/></Relationships>' });
  files.push({ name: 'xl/workbook.xml', data: '<?xml version="1.0" encoding="UTF-8" standalone="yes"?><workbook xmlns="http://schemas.openxmlformats.org/spreadsheetml/2006/main" xmlns:r="http://schemas.openxmlformats.org/officeDocument/2006/relationships"><sheets>' + sheets.map((s, i) => `<sheet name="${xmlEsc(s.name.slice(0, 31))}" sheetId="${i + 1}" r:id="rId${i + 1}"/>`).join('') + '</sheets></workbook>' });
  files.push({ name: 'xl/_rels/workbook.xml.rels', data: '<?xml version="1.0" encoding="UTF-8" standalone="yes"?><Relationships xmlns="http://schemas.openxmlformats.org/package/2006/relationships">' + sheets.map((s, i) => `<Relationship Id="rId${i + 1}" Type="http://schemas.openxmlformats.org/officeDocument/2006/relationships/worksheet" Target="worksheets/sheet${i + 1}.xml"/>`).join('') + `<Relationship Id="rId${sheets.length + 1}" Type="http://schemas.openxmlformats.org/officeDocument/2006/relationships/styles" Target="styles.xml"/></Relationships>` });
  // 樣式: 0 一般, 1 表頭(粗體灰底), 2 數字 #,##0.00, 3 粗體, 4 粗體數字
  files.push({ name: 'xl/styles.xml', data: '<?xml version="1.0" encoding="UTF-8" standalone="yes"?><styleSheet xmlns="http://schemas.openxmlformats.org/spreadsheetml/2006/main"><numFmts count="1"><numFmt numFmtId="164" formatCode="#,##0.00"/></numFmts><fonts count="3"><font><sz val="11"/><name val="Microsoft JhengHei"/></font><font><b/><sz val="11"/><name val="Microsoft JhengHei"/></font><font><b/><sz val="14"/><name val="Microsoft JhengHei"/></font></fonts><fills count="3"><fill><patternFill patternType="none"/></fill><fill><patternFill patternType="gray125"/></fill><fill><patternFill patternType="solid"><fgColor rgb="FFE8EEF4"/></patternFill></fill></fills><borders count="2"><border/><border><left style="thin"><color rgb="FFBFBFBF"/></left><right style="thin"><color rgb="FFBFBFBF"/></right><top style="thin"><color rgb="FFBFBFBF"/></top><bottom style="thin"><color rgb="FFBFBFBF"/></bottom></border></borders><cellStyleXfs count="1"><xf/></cellStyleXfs><cellXfs count="6"><xf fontId="0" borderId="1" applyBorder="1"/><xf fontId="1" fillId="2" borderId="1" applyFont="1" applyFill="1" applyBorder="1"/><xf fontId="0" numFmtId="164" borderId="1" applyNumberFormat="1" applyBorder="1"/><xf fontId="1" borderId="1" applyFont="1" applyBorder="1"/><xf fontId="1" numFmtId="164" borderId="1" applyFont="1" applyNumberFormat="1" applyBorder="1"/><xf fontId="2" applyFont="1"/></cellXfs><cellStyles count="1"><cellStyle name="Normal" xfId="0" builtinId="0"/></cellStyles></styleSheet>' });
  sheets.forEach((s, si) => {
    let x = '<?xml version="1.0" encoding="UTF-8" standalone="yes"?><worksheet xmlns="http://schemas.openxmlformats.org/spreadsheetml/2006/main">';
    if (s.freeze) x += `<sheetViews><sheetView workbookViewId="0"><pane ySplit="${s.freeze}" topLeftCell="A${s.freeze + 1}" activePane="bottomLeft" state="frozen"/></sheetView></sheetViews>`;
    if (s.widths) x += '<cols>' + s.widths.map((w, i) => `<col min="${i + 1}" max="${i + 1}" width="${w}" customWidth="1"/>`).join('') + '</cols>';
    x += '<sheetData>';
    s.rows.forEach((row, ri) => {
      x += `<row r="${ri + 1}">`;
      row.forEach((cell, ci) => {
        if (cell === null || cell === undefined || cell === '') return;
        const ref = colName(ci) + (ri + 1);
        let v = cell, st = null;
        if (typeof cell === 'object') { v = cell.v; st = cell.s; }
        if (typeof v === 'number' && isFinite(v)) x += `<c r="${ref}" s="${st != null ? st : 2}"><v>${Math.round(v * 1e6) / 1e6}</v></c>`;
        else x += `<c r="${ref}" t="inlineStr" s="${st != null ? st : 0}"><is><t xml:space="preserve">${xmlEsc(v)}</t></is></c>`;
      });
      x += '</row>';
    });
    x += '</sheetData></worksheet>';
    files.push({ name: `xl/worksheets/sheet${si + 1}.xml`, data: x });
  });
  return zipStore(files);
}

/* 由圖名自動找平面圖範圍 */
const CN = { 零: 0, 一: 1, 二: 2, 兩: 2, 三: 3, 四: 4, 五: 5, 六: 6, 七: 7, 八: 8, 九: 9, 十: 10 };
function cnNum(s) {
  if (/^\d+$/.test(s)) return parseInt(s);
  let v = 0, cur = 0;
  for (const ch of s) { const d = CN[ch]; if (d === undefined) return NaN; if (d === 10) { v += (cur || 1) * 10; cur = 0; } else cur = d; }
  return v + cur;
}
function floorRepeat(title) {
  const m = /([\d一二三四五六七八九十]+)\s*[至~\-~到]\s*([\d一二三四五六七八九十]+)\s*[層樓F]/.exec(title);
  if (m) { const a = cnNum(m[1]), b = cnNum(m[2]); if (b >= a) return b - a + 1; }
  const m2 = /([\d一二三四五六七八九十]+)\s*[、,,及]\s*([\d一二三四五六七八九十]+)\s*[層樓F]/.exec(title);
  if (m2) return 2;
  return 1;
}
function findPlanTitles(F) {
  const ts = F.texts.filter(t => /平面圖/.test(t.s) && t.s.length <= 16 && !/、|,|及|結構|面積|單線|天花|反射|配置|陰影|日照|檢討|無障礙|台電|配電/.test(t.s));
  // 同一位置重複者去除
  const out = [];
  for (const t of ts.sort((a, b) => b.h - a.h)) {
    if (out.some(o => o.s === t.s && Math.hypot(o.x - t.x, o.y - t.y) < t.h * 5)) continue;
    out.push(t);
  }
  // 同一個圖名出現多次時,只留字高接近最大的(圖框標題欄、圖說裡的小字不是平面圖)
  const maxH = {}; for (const t of out) maxH[t.s] = Math.max(maxH[t.s] || 0, t.h || 0);
  for (let i = out.length - 1; i >= 0; i--) if ((out[i].h || 0) < maxH[out[i].s] * 0.6) out.splice(i, 1);
  // 照樓層由下往上排:地下 → 一層 → 夾層 → … → 屋突 → 屋頂
  const lv = s => {
    const m = /([\d一二三四五六七八九十兩]+)\s*(?:夾層|[層樓F])/.exec(s); const n = m ? cnNum(m[1]) : NaN;
    if (/屋頂/.test(s) && !/屋突/.test(s)) return 2000;
    if (/屋突/.test(s)) return 1000 + (isNaN(n) ? 0 : n);
    if (/地下/.test(s)) return -(isNaN(n) ? 1 : n);
    return (isNaN(n) ? 500 : n) + (/夾層/.test(s) ? 0.5 : 0);
  };
  out.sort((a, b) => lv(a.s) - lv(b.s));
  return out.map(t => ({ title: t.s, x: t.x, y: t.y, h: t.h, repeat: floorRepeat(t.s) }));
}
function planBoxNearTitle(F, t, layerRoles, opt) {
  opt = opt || {};
  const h = t.h || 100;
  const win = [t.x - (opt.wx || 30) * h, t.y - 5 * h, t.x + (opt.wx || 30) * h, t.y + (opt.wy || 45) * h];
  const isWall = F.layerNames.map(n => { const r = (layerRoles[n] || guessRole(n)).role; return opt.members ? opt.members.indexOf(r) >= 0 : (r.startsWith('wall_') || r === 'column' || r === 'rail'); });
  const cand = F.polys.filter(p => isWall[p.L] && p.bb[0] >= win[0] && p.bb[2] <= win[2] && p.bb[1] >= win[1] && p.bb[3] <= win[3]);
  if (!cand.length) return null;
  // 從圖名上方最近的牆開始,逐步併入相鄰圖元
  const target = [t.x, t.y + 8 * h];
  let best = null, bd = Infinity;
  for (const p of cand) { const cx = (p.bb[0] + p.bb[2]) / 2, cy = (p.bb[1] + p.bb[3]) / 2; if (cy < t.y) continue; const d = Math.hypot(cx - target[0], cy - target[1]); if (d < bd) { bd = d; best = p; } }
  if (!best) return null;
  let bb = best.bb.slice();
  const gap = (opt.gap || 3) * h;
  let used = new Uint8Array(cand.length);
  let changed = true, guard = 0;
  while (changed && guard++ < 60) {
    changed = false;
    for (let i = 0; i < cand.length; i++) {
      if (used[i]) continue; const q = cand[i].bb;
      if (q[0] > bb[2] + gap || q[2] < bb[0] - gap || q[1] > bb[3] + gap || q[3] < bb[1] - gap) continue;
      used[i] = 1; bb = [Math.min(bb[0], q[0]), Math.min(bb[1], q[1]), Math.max(bb[2], q[2]), Math.max(bb[3], q[3])]; changed = true;
    }
  }
  const m = 1.5 * h;
  return [bb[0] - m, bb[1] - m, bb[2] + m, bb[3] + m];
}
function detectUnit(F, insunits) {
  // 以門圖塊寬度中位數判斷(門寬約 70~120 cm)
  const doorL = new Set(); F.layerNames.forEach((n, i) => { if (guessRole(n).role === 'door') doorL.add(i); });
  const ws = [];
  for (const ins of F.inserts) if (doorL.has(ins.L) && ins.box) { const w = Math.max(ins.w, ins.h); if (w > 0) ws.push(w); }
  if (ws.length >= 3) {
    ws.sort((a, b) => a - b); const m = ws[ws.length >> 1];
    if (m > 400 && m < 2000) return { unitToCm: 0.1, why: '門寬約 ' + Math.round(m) + ' 單位 → mm' };
    if (m > 40 && m < 200) return { unitToCm: 1, why: '門寬約 ' + Math.round(m) + ' 單位 → cm' };
    if (m > 0.4 && m < 2) return { unitToCm: 100, why: '門寬約 ' + m.toFixed(2) + ' 單位 → m' };
  }
  const map = { 4: 0.1, 5: 1, 6: 100, 1: 2.54, 2: 30.48 };
  if (map[insunits]) return { unitToCm: map[insunits], why: '依檔案單位設定' };
  return { unitToCm: 1, why: '無法判斷,預設 cm' };
}

/* ------------------------------------------------------------------ */
/* 9. 立面分析                                                          */
/* ------------------------------------------------------------------ */
const EROLES = { ignore: '忽略', outline: '外牆輪廓', opening: '開口(門窗)', rail: '欄杆/透空', material: '材料填充' };
function guessElevRole(name, hasHatch) {
  const r = guessRole(name).role;
  if (hasHatch && /磚|石|丁掛|塗|漆|材|面|EH|洗石|抿石|板|TILE|STONE|PAINT/i.test(name) && !/窗|門|WIN|DOOR|玻璃/i.test(name)) return { role: 'material' };
  if (r === 'window' || r === 'door' || /鋁門窗|帷幕|玻璃(?!欄)/.test(name)) return { role: 'opening' };
  if (r === 'rail' || /欄杆|格柵|百葉|透空/.test(name)) return { role: 'rail' };
  if (r.startsWith('wall_') || r === 'column' || /ELEV|立面線|外牆|輪廓|OUTLINE/i.test(name)) return { role: 'outline' };
  return { role: 'ignore' };
}
function materialName(layer) {
  return layer.replace(/^[\dA-Z]{0,3}[-_ ]*(EH|E|A|ID)?[-_ ]*/i, '').replace(/^[-_ ]+/, '') || layer;
}
function guessTileSize(name) {
  if (/二丁掛/.test(name)) return '22.7x6';
  if (/小口/.test(name)) return '10.8x6';
  if (/丁掛/.test(name)) return '22.7x6';
  if (/馬賽克|馬賽克/.test(name)) return '';
  return '';
}
function fillPolyRaster(M, nx, ny, loops, X, Y, val, mask) {
  // 偶奇規則掃描線填色;loops 為世界座標
  const edges = [];
  let ymin = Infinity, ymax = -Infinity;
  for (const lp of loops) {
    const n = lp.length;
    for (let i = 0; i < n; i += 2) {
      const j = (i + 2) % n;
      const x1 = X(lp[i]), y1 = Y(lp[i + 1]), x2 = X(lp[j]), y2 = Y(lp[j + 1]);
      if (y1 === y2) continue;
      edges.push([x1, y1, x2, y2]);
      ymin = Math.min(ymin, y1, y2); ymax = Math.max(ymax, y1, y2);
    }
  }
  ymin = Math.max(0, Math.floor(ymin)); ymax = Math.min(ny - 1, Math.ceil(ymax));
  const xs = [];
  for (let y = ymin; y <= ymax; y++) {
    const yc = y + 0.5; xs.length = 0;
    for (const e of edges) {
      const [x1, y1, x2, y2] = e;
      if ((yc >= y1 && yc < y2) || (yc >= y2 && yc < y1)) xs.push(x1 + (yc - y1) * (x2 - x1) / (y2 - y1));
    }
    xs.sort((a, b) => a - b);
    for (let k = 0; k + 1 < xs.length; k += 2) {
      const a = Math.max(0, Math.ceil(xs[k] - 0.5)), b = Math.min(nx - 1, Math.floor(xs[k + 1] - 0.5));
      for (let x = a; x <= b; x++) { const i = y * nx + x; if (!mask || mask[i]) M[i] = val; }
    }
  }
}
function analyzeElevation(F, box, eroles, params, zones, defaultMat) {
  const U = params.unitToCm;
  const roleOf = F.layerNames.map(n => (eroles[n] || { role: 'ignore' }).role);
  const W = box[2] - box[0], H = box[3] - box[1];
  const px = Math.max(1 / U, Math.max(W, H) / 2400);
  const nx = Math.ceil(W / px) + 2, ny = Math.ceil(H / px) + 2, N = nx * ny;
  const X = x => (x - box[0]) / px + 1, Y = y => (y - box[1]) / px + 1;
  const XI = x => Math.floor(X(x)), YI = y => Math.floor(Y(y));
  const polys = F.polys.filter(p => !(p.bb[2] < box[0] || p.bb[0] > box[2] || p.bb[3] < box[1] || p.bb[1] > box[3]));
  const outl = new Uint8Array(N), openL = new Uint8Array(N); // openL: 1 門窗線, 2 欄杆線
  function line(x0, y0, x1, y1, M, v) {
    let ax = XI(x0), ay = YI(y0), bx = XI(x1), by = YI(y1);
    const dx = Math.abs(bx - ax), dy = Math.abs(by - ay), sx = ax < bx ? 1 : -1, sy = ay < by ? 1 : -1;
    let err = dx - dy, guard = 0;
    while (true) {
      if (ax >= 0 && ay >= 0 && ax < nx && ay < ny) M[ay * nx + ax] = v;
      if (ax === bx && ay === by) break;
      if (++guard > 20000) break;
      const e2 = 2 * err; if (e2 > -dy) { err -= dy; ax += sx; } if (e2 < dx) { err += dx; ay += sy; }
    }
  }
  for (const p of polys) {
    const r = roleOf[p.L];
    if (r !== 'outline' && r !== 'opening' && r !== 'rail') continue;
    const q = p.p;
    for (let i = 0; i + 3 < q.length; i += 2) {
      line(q[i], q[i + 1], q[i + 2], q[i + 3], outl, 1);
      if (r !== 'outline') line(q[i], q[i + 1], q[i + 2], q[i + 3], openL, r === 'rail' ? 2 : 1);
    }
  }
  // 外輪廓:外部填色,失敗時改用逐列左右端
  const od = dilate(outl, nx, ny, 1);
  const lab = new Int32Array(N);
  for (let i = 0; i < N; i++) if (od[i]) lab[i] = -2;
  const seeds = []; for (let x = 0; x < nx; x++) { seeds.push(x, (ny - 1) * nx + x); } for (let y = 0; y < ny; y++) { seeds.push(y * nx, y * nx + nx - 1); }
  floodFill(lab, nx, ny, seeds, -1, 0);
  const sil1 = new Uint8Array(N); let a1 = 0;
  for (let i = 0; i < N; i++) if (lab[i] !== -1) { sil1[i] = 1; a1++; }
  const sil2 = new Uint8Array(N); let a2 = 0;
  for (let y = 0; y < ny; y++) {
    let l = -1, r = -1; const row = y * nx;
    for (let x = 0; x < nx; x++) if (outl[row + x]) { if (l < 0) l = x; r = x; }
    if (l >= 0) for (let x = l; x <= r; x++) { sil2[row + x] = 1; a2++; }
  }
  let sil = sil1, method = 'outline';
  if (a1 < a2 * 0.6) { sil = sil2; method = 'rowspan'; }
  // 開口:輪廓內、被門窗/欄杆線圍住的小區塊
  const comp = new Int32Array(N); // 0 未處理
  const cls = [0]; // 1 牆, 2 開口, 3 欄杆
  let nc = 0;
  const stack = new Int32Array(N);
  const cellA = (px * U) * (px * U) / 1e4;
  for (let s0 = 0; s0 < N; s0++) {
    if (!sil[s0] || openL[s0] || comp[s0]) continue;
    nc++; let sp = 0; stack[sp++] = s0; comp[s0] = nc; let cnt = 0, tWin = 0, tRail = 0, tOther = 0;
    while (sp) {
      const i = stack[--sp]; cnt++;
      const x = i % nx;
      const nb = [x > 0 ? i - 1 : -1, x < nx - 1 ? i + 1 : -1, i - nx, i + nx];
      for (const j of nb) {
        if (j < 0 || j >= N) { tOther++; continue; }
        if (!sil[j]) { tOther++; continue; }
        if (openL[j]) { if (openL[j] === 2) tRail++; else tWin++; continue; }
        if (!comp[j]) { comp[j] = nc; stack[sp++] = j; }
      }
    }
    const tot = tWin + tRail + tOther;
    let c = 1;
    if (tot && tOther / tot < 0.08 && cnt * cellA < 60) c = tRail > tWin ? 3 : 2;
    cls.push(c);
  }
  // 最大區塊一定是牆
  // 線條像素歸屬相鄰區塊
  const kind = new Uint8Array(N); // 0 外, 1 牆, 2 開口, 3 欄杆
  for (let i = 0; i < N; i++) if (sil[i]) kind[i] = comp[i] ? cls[comp[i]] : 0;
  for (let i = 0; i < N; i++) if (sil[i] && !comp[i]) {
    const x = i % nx; let k = 1;
    for (const j of [x > 0 ? i - 1 : -1, x < nx - 1 ? i + 1 : -1, i - nx, i + nx]) if (j >= 0 && j < N && comp[j] && cls[comp[j]] > 1) { k = cls[comp[j]]; break; }
    kind[i] = k;
  }
  // 材料:填充線 → 使用者分區
  const mats = [defaultMat || '外牆(未分區)'];
  const matIdx = new Uint16Array(N);
  const wallMask = new Uint8Array(N); for (let i = 0; i < N; i++) wallMask[i] = kind[i] === 1 ? 1 : 0;
  for (const h of F.hatches || []) {
    if (roleOf[h.L] !== 'material') continue;
    if (h.bb[2] < box[0] || h.bb[0] > box[2] || h.bb[3] < box[1] || h.bb[1] > box[3]) continue;
    const nm = materialName(F.layerNames[h.L]);
    let mi = mats.indexOf(nm); if (mi < 0) { mi = mats.length; mats.push(nm); }
    const tmp = new Uint8Array(N);
    fillPolyRaster(tmp, nx, ny, h.loops, X, Y, 1, null);
    for (let i = 0; i < N; i++) if (tmp[i] && wallMask[i]) matIdx[i] = mi;
  }
  for (const z of zones || []) {
    const b = z.box; if (b[2] < box[0] || b[0] > box[2] || b[3] < box[1] || b[1] > box[3]) continue;
    if (z.mat === '不計') {
      const x0 = Math.max(0, XI(b[0])), x1 = Math.min(nx - 1, XI(b[2])), y0 = Math.max(0, YI(b[1])), y1 = Math.min(ny - 1, YI(b[3]));
      for (let y = y0; y <= y1; y++) for (let x = x0; x <= x1; x++) { const i = y * nx + x; kind[i] = 0; wallMask[i] = 0; }
      continue;
    }
    let mi = mats.indexOf(z.mat); if (mi < 0) { mi = mats.length; mats.push(z.mat); }
    const x0 = Math.max(0, XI(b[0])), x1 = Math.min(nx - 1, XI(b[2])), y0 = Math.max(0, YI(b[1])), y1 = Math.min(ny - 1, YI(b[3]));
    for (let y = y0; y <= y1; y++) for (let x = x0; x <= x1; x++) { const i = y * nx + x; if (wallMask[i]) matIdx[i] = mi; }
  }
  const matArea = mats.map(() => 0);
  let facade = 0, open = 0, rail = 0, wall = 0, nOpen = 0;
  for (let i = 0; i < N; i++) {
    const k = kind[i]; if (!k) continue;
    facade++;
    if (k === 1) { wall++; matArea[matIdx[i]]++; } else if (k === 2) open++; else rail++;
  }
  for (let c = 1; c < cls.length; c++) if (cls[c] === 2) nOpen++;
  // 寬、高
  let minx = nx, maxx = -1, miny = ny, maxy = -1;
  for (let y = 0; y < ny; y++) for (let x = 0; x < nx; x++) if (kind[y * nx + x]) { if (x < minx) minx = x; if (x > maxx) maxx = x; if (y < miny) miny = y; if (y > maxy) maxy = y; }
  return {
    kind: 'elev', box, px, nx, ny, raster: kind, matIdx, mats, method,
    facade: facade * cellA, open: open * cellA, rail: rail * cellA, wall: wall * cellA,
    matAreas: mats.map((m, i) => ({ name: m, area: matArea[i] * cellA })).filter(m => m.area > 0.01),
    openCount: nOpen, width: maxx >= minx ? (maxx - minx + 1) * px * U / 100 : 0, height: maxy >= miny ? (maxy - miny + 1) * px * U / 100 : 0,
  };
}
function elevationItems(E, params, opt) {
  // opt: { returnPct, tileSizes:{name:size} }
  const k = 1 + (opt.returnPct || 0) / 100;
  const items = [];
  const add = (trade, item, unit, qty, lossKey, note) => { if (qty > 1e-6) items.push({ trade, item, unit, qty, lossKey, note: note || '' }); };
  add('泥作', '外牆 1:3 水泥砂漿打底', 'm²', E.wall * k, 'mortar', `立面淨面積 ${E.wall.toFixed(1)} m²${opt.returnPct ? ` × (1+${opt.returnPct}% 凹凸補正)` : ''}`);
  for (const m of E.matAreas) {
    const a = m.area * k;
    const isPaint = /漆|塗/.test(m.name), isStone = /石材|花崗|大理/.test(m.name);
    const trade = isPaint ? '油漆' : isStone ? '石材' : '磁磚';
    add(trade, '外牆 ' + m.name, 'm²', a, isPaint ? 'paint' : 'tile');
    const sz = (opt.tileSizes && opt.tileSizes[m.name]) || guessTileSize(m.name);
    const mm = /([\d.]+)\s*[x×*]\s*([\d.]+)/.exec(sz || '');
    if (!isPaint && !isStone && mm) { const j = (opt.joint == null ? 1 : opt.joint); const per = 1e4 / ((parseFloat(mm[1]) + j) * (parseFloat(mm[2]) + j)); add('磁磚', `外牆 ${m.name} 片數`, '片', a * per, 'tile', `${sz} cm,灰縫 ${j} cm,約 ${per.toFixed(0)} 片/m²`); }
  }
  add('其他', '外牆開口(門窗)面積', 'm²', E.open, 'paint', `${E.openCount} 處,已自立面扣除`);
  if (E.rail > 0.01) add('其他', '欄杆/透空面積', 'm²', E.rail, 'paint', '已自立面扣除');
  const TO = ['結構', '泥作', '磁磚', '石材', '油漆', '其他'];
  items.sort((a, b) => TO.indexOf(a.trade) - TO.indexOf(b.trade));
  for (const it of items) { const l = it.trade === '其他' ? 0 : (params.loss[it.lossKey] || 0); it.loss = l; it.total = it.qty * (1 + l / 100); }
  return items;
}

const api = { EROLES, guessElevRole, materialName, analyzeElevation, elevationItems, findPlanTitles, planBoxNearTitle, floorRepeat, detectUnit, mergedType, parseDXF, flattenDXF, guessRole, ROLES, ROOM_TYPES, roomTypeOf, isRoomLabel, defaultFinishes, defaultParams, analyzeRegion, computeQuantities, buildXLSX, decodeBytes, cleanMText, tileArea };
if (typeof module !== 'undefined' && module.exports) module.exports = api; else root.QE = api;
})(typeof window !== 'undefined' ? window : globalThis);
