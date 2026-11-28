// Optimal-parse DEFLATE for the PNG squeezer: a zopfli-style encoder
// written for this entry. It takes the filtered bytes of one image and
// returns one zlib stream holding one or more dynamic-Huffman blocks, or
// null when it cannot.
//
// Design:
//  * 3-byte hash chains (length-3 matches included), previous-match
//    extension for runs, three distance tiers, and structural candidates
//    (a run is one pixel back, a repeated row is one row back) whose
//    lengths are tracked incrementally from the previous position, so a
//    long structural match costs a couple of compares a position. The
//    chain walk never bails out early on a merely "good" match: a
//    32-byte match must not hide a 258-byte one.
//  * Integer (exact-bit) shortest-path parse, precomputed offer lists per
//    match length, 3 refinement passes (fixed lengths, then rebuilt
//    tables, twice).
//  * Token-level block splitting: the token stream is split at row
//    boundaries into blocks, each with its own Huffman tables; candidate
//    granularities are emitted for real and the smallest wins.
//  * Fixed-Huffman blocks when they beat dynamic ones.
//  * Everything is deterministic: fixed chain limits, fixed iteration
//    counts, no clock, no randomness.

const MIN_MATCH = 3;
const MAX_MATCH = 258;
const WSIZE = 32768;
const HASH_BITS = 15;
const HASH_SIZE = 1 << HASH_BITS;
const HASH_MASK = HASH_SIZE - 1;
const NEAR_DIST = 256;
const MID_DIST = 2048;

const LEN_BASE = [3, 4, 5, 6, 7, 8, 9, 10, 11, 13, 15, 17, 19, 23, 27, 31, 35, 43, 51, 59, 67, 83, 99, 115, 131, 163, 195, 227, 258];
const LEN_EXTRA = [0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 2, 2, 2, 2, 3, 3, 3, 3, 4, 4, 4, 4, 5, 5, 5, 5, 0];
const DIST_BASE = [1, 2, 3, 4, 5, 7, 9, 13, 17, 25, 33, 49, 65, 97, 129, 193, 257, 385, 513, 769, 1025, 1537, 2049, 3073, 4097, 6145, 8193, 12289, 16385, 24577];
const DIST_EXTRA = [0, 0, 0, 0, 1, 1, 2, 2, 3, 3, 4, 4, 5, 5, 6, 6, 7, 7, 8, 8, 9, 9, 10, 10, 11, 11, 12, 12, 13, 13];

const LEN_CODE_OF = new Int32Array(259);
const LEN_EXT_OF = new Int32Array(259);
for (let c = 0; c < 29; c++) {
  const hi = c === 28 ? 258 : LEN_BASE[c + 1] - 1;
  for (let l = LEN_BASE[c]; l <= hi; l++) { LEN_CODE_OF[l] = c; LEN_EXT_OF[l] = LEN_EXTRA[c]; }
}
const DIST_CODE_OF = new Int32Array(WSIZE + 1);
const DIST_EXT_OF = new Int32Array(WSIZE + 1);
for (let c = 0; c < 30; c++) {
  const hi = c === 29 ? WSIZE : DIST_BASE[c + 1] - 1;
  for (let d = DIST_BASE[c]; d <= hi; d++) { DIST_CODE_OF[d] = c; DIST_EXT_OF[d] = DIST_EXTRA[c]; }
}

// OFFER[L]: the lengths to try for a match of length L (longest length of
// each length code <= L), as a flat table with offsets.
const OFFER_OFF = new Int32Array(260);
const OFFER_VALS = [];
for (let L = 0; L <= 259; L++) {
  OFFER_OFF[L] = OFFER_VALS.length;
  for (let c = 0; c < 29; c++) {
    if (LEN_BASE[c] > L) break;
    OFFER_VALS.push(Math.min(c === 28 ? 258 : LEN_BASE[c + 1] - 1, L));
  }
}
OFFER_OFF[259] = OFFER_VALS.length;
const OFFER = Int32Array.from(OFFER_VALS);

const FIXED_LIT_LEN = new Int32Array(286);
for (let s = 0; s < 286; s++) FIXED_LIT_LEN[s] = s < 144 ? 8 : s < 256 ? 9 : s < 280 ? 7 : 8;
const FIXED_DIST_LEN = new Int32Array(30).fill(5);

function adler32(data) {
  let a = 1, b = 0;
  for (let i = 0; i < data.length;) {
    const end = Math.min(data.length, i + 5552);
    for (; i < end; i++) { a += data[i]; b += a; }
    a %= 65521; b %= 65521;
  }
  return ((b << 16) | a) >>> 0;
}

class BitWriter {
  constructor(capacity) { this.out = new Uint8Array(capacity); this.at = 0; this.bitbuf = 0; this.bitcnt = 0; }
  writeBits(value, count) {
    this.bitbuf |= value << this.bitcnt;
    this.bitcnt += count;
    while (this.bitcnt >= 8) { this.out[this.at++] = this.bitbuf & 0xff; this.bitbuf >>>= 8; this.bitcnt -= 8; }
  }
  finish() {
    if (this.bitcnt > 0) { this.out[this.at++] = this.bitbuf & 0xff; this.bitbuf = 0; this.bitcnt = 0; }
    return this.out.subarray(0, this.at);
  }
}

function buildLengths(freq, maxBits) {
  const n = freq.length;
  const lengths = new Int32Array(n);
  const used = [];
  for (let s = 0; s < n; s++) if (freq[s] > 0) used.push(s);
  if (used.length === 0) return lengths;
  if (used.length === 1) { lengths[used[0]] = 1; return lengths; }
  const heapFreq = [], heapId = [];
  const nodeFreq = new Float64Array(2 * n);
  const nodeLeft = new Int32Array(2 * n).fill(-1);
  const nodeRight = new Int32Array(2 * n).fill(-1);
  let nodes = 0;
  const heapPush = (f, id) => {
    heapFreq.push(f); heapId.push(id);
    let i = heapFreq.length - 1;
    while (i > 0) {
      const p = (i - 1) >> 1;
      if (heapFreq[p] < heapFreq[i] || (heapFreq[p] === heapFreq[i] && heapId[p] < heapId[i])) break;
      [heapFreq[p], heapFreq[i]] = [heapFreq[i], heapFreq[p]];
      [heapId[p], heapId[i]] = [heapId[i], heapId[p]];
      i = p;
    }
  };
  const heapPop = () => {
    const topF = heapFreq[0], topId = heapId[0];
    const lastF = heapFreq.pop(), lastId = heapId.pop();
    if (heapFreq.length > 0) {
      heapFreq[0] = lastF; heapId[0] = lastId;
      let i = 0;
      for (;;) {
        const l = i * 2 + 1, r = l + 1;
        let m = i;
        if (l < heapFreq.length && (heapFreq[l] < heapFreq[m] || (heapFreq[l] === heapFreq[m] && heapId[l] < heapId[m]))) m = l;
        if (r < heapFreq.length && (heapFreq[r] < heapFreq[m] || (heapFreq[r] === heapFreq[m] && heapId[r] < heapId[m]))) m = r;
        if (m === i) break;
        [heapFreq[m], heapFreq[i]] = [heapFreq[i], heapFreq[m]];
        [heapId[m], heapId[i]] = [heapId[i], heapId[m]];
        i = m;
      }
    }
    return [topF, topId];
  };
  for (const s of used) { nodeFreq[nodes] = freq[s]; heapPush(freq[s], nodes); nodes++; }
  let nextId = n;
  const leafNodeOf = new Int32Array(n).fill(-1);
  for (let k = 0; k < used.length; k++) leafNodeOf[used[k]] = k;
  while (heapFreq.length > 1) {
    const [f1, id1] = heapPop();
    const [f2, id2] = heapPop();
    nodeFreq[nextId] = f1 + f2;
    nodeLeft[nextId] = id1; nodeRight[nextId] = id2;
    heapPush(f1 + f2, nextId);
    nextId++;
  }
  const root = heapId[0];
  const stack = [[root, 0]];
  const depthOf = new Int32Array(nextId);
  while (stack.length > 0) {
    const [id, d] = stack.pop();
    depthOf[id] = d;
    if (nodeLeft[id] !== -1) { stack.push([nodeLeft[id], d + 1]); stack.push([nodeRight[id], d + 1]); }
  }
  const blCount = new Int32Array(maxBits + 1);
  let overflow = 0;
  for (const s of used) {
    const d = depthOf[leafNodeOf[s]];
    if (d > maxBits) { overflow++; blCount[maxBits]++; } else blCount[d]++;
  }
  if (overflow > 0) {
    let excess = 0;
    for (let b = 1; b <= maxBits; b++) excess += blCount[b] * (1 << (maxBits - b));
    excess -= 1 << maxBits;
    while (excess > 0) {
      let m = maxBits - 1;
      while (blCount[m] === 0) m--;
      blCount[m]--; blCount[m + 1] += 2; blCount[maxBits]--; excess--;
    }
  }
  const byFreq = [...used].sort((a, b) => freq[b] - freq[a] || a - b);
  let k = 0;
  for (let b = 1; b <= maxBits; b++) for (let j = 0; j < blCount[b]; j++) lengths[byFreq[k++]] = b;
  return lengths;
}

function canonicalCodes(lengths) {
  const n = lengths.length;
  const codes = new Int32Array(n);
  const count = new Int32Array(16);
  for (let s = 0; s < n; s++) if (lengths[s] > 0) count[lengths[s]]++;
  const next = new Int32Array(16);
  let code = 0;
  for (let b = 1; b < 16; b++) { code = (code + count[b - 1]) << 1; next[b] = code; }
  for (let s = 0; s < n; s++) { const len = lengths[s]; if (len > 0) codes[s] = next[len]++; }
  return codes;
}

function reverseBits(code, length) {
  let r = 0;
  for (let i = 0; i < length; i++) { r = (r << 1) | (code & 1); code >>>= 1; }
  return r;
}

function hash3(data, i) {
  return (Math.imul(((data[i] << 16) ^ (data[i + 1] << 8) ^ data[i + 2]), 2654435761) >>> 17) & HASH_MASK;
}

/**
 * Longest match at every position, three distance tiers. Chain limit and
 * good-match cutoff are parameters so the caller can trade speed for size.
 * `rowLen` seeds structural candidates: in screenshots the dominant long
 * matches are a row back (distance rowLen, 2*rowLen, ...) or a run
 * (distance 1..4), so those distances are always tested directly instead
 * of relying on the hash chain to reach them. The chain walk never bails
 * out early on a merely "good" match: a 32-byte match must not hide a
 * 258-byte one (the walk only stops at the chain limit or the window edge).
 */
function findMatches(data, rowLen, maxChain, goodMatch, structGate = 128) {
  const n = data.length;
  const lens = new Uint16Array(n), dists = new Uint16Array(n);
  const nearLens = new Uint16Array(n), nearDists = new Uint16Array(n);
  const midLens = new Uint16Array(n), midDists = new Uint16Array(n);
  const head = new Int32Array(HASH_SIZE).fill(-1);
  const prev = new Int32Array(n).fill(-1);
  // Structural distances, tested directly at every position: a run is a
  // match at distance bpp (one pixel back), a repeated row at rowLen.
  // bpp = (rowLen - 1) / 1280 for these 1280-wide images. Their lengths
  // are tracked incrementally: the length at position i is the length at
  // i - 1 minus one, extended, so a long structural match costs a couple
  // of compares a position instead of a fresh 258-byte scan.
  const bpp = Math.max(1, Math.round((rowLen - 1) / 1280));
  const structD = [1, bpp, rowLen, 2 * rowLen, 3 * rowLen].filter((d, k, a) => a.indexOf(d) === k);
  const sLen = new Int32Array(structD.length);
  let prevLen = 0, prevDist = 0, prevNearLen = 0, prevNearDist = 0, prevMidLen = 0, prevMidDist = 0;
  for (let i = 0; i < n; i++) {
    let bestLen = 0, bestDist = 0, nearLen = 0, nearDist = 0, midLen = 0, midDist = 0;
    if (i + 3 <= n) {
      const maxL = Math.min(MAX_MATCH, n - i);
      if (prevLen > 1 && prevDist > 0) {
        const cand = i - prevDist;
        let l = Math.min(prevLen - 1, maxL);
        while (l < maxL && data[cand + l] === data[i + l]) l++;
        bestLen = l; bestDist = prevDist;
        if (prevDist <= MID_DIST) { midLen = l; midDist = prevDist; }
        if (prevDist <= NEAR_DIST) { nearLen = l; nearDist = prevDist; }
      }
      if (prevMidLen > 1 && prevMidDist > 0 && prevMidDist !== prevDist) {
        const cand = i - prevMidDist;
        let l = Math.min(prevMidLen - 1, maxL);
        while (l < maxL && data[cand + l] === data[i + l]) l++;
        if (l > midLen) { midLen = l; midDist = prevMidDist; }
        if (prevMidDist <= NEAR_DIST && l > nearLen) { nearLen = l; nearDist = prevMidDist; }
      }
      if (prevNearLen > 1 && prevNearDist > 0 && prevNearDist !== prevDist && prevNearDist !== prevMidDist) {
        const cand = i - prevNearDist;
        let l = Math.min(prevNearLen - 1, maxL);
        while (l < maxL && data[cand + l] === data[i + l]) l++;
        if (l > nearLen) { nearLen = l; nearDist = prevNearDist; }
      }
      // Structural candidates, lengths tracked incrementally from the
      // previous position: a match of length L at i - 1 is a match of
      // length L - 1 at i, extended only past its old end.
      for (let s = 0; s < structD.length; s++) {
        const d = structD[s];
        if (d > i) { sLen[s] = 0; continue; }
        const cand = i - d;
        let l;
        if (sLen[s] > 1) {
          l = sLen[s] - 1;
          while (l < maxL && data[cand + l] === data[i + l]) l++;
        } else {
          if (data[cand] !== data[i] || data[cand + 1] !== data[i + 1] || data[cand + 2] !== data[i + 2]) { sLen[s] = 0; continue; }
          l = 3;
          while (l < maxL && data[cand + l] === data[i + l]) l++;
        }
        sLen[s] = l;
        if (l < MIN_MATCH) continue;
        if (l > bestLen) { bestLen = l; bestDist = d; }
        if (d <= MID_DIST && l > midLen) { midLen = l; midDist = d; }
        if (d <= NEAR_DIST && l > nearLen) { nearLen = l; nearDist = d; }
      }
      if (bestLen < maxL) {
        const h = hash3(data, i);
        let cand = head[h];
        let chain = 0;
        // Once a good match exists, the walk may stop sooner, but it never
        // stops outright: the limit only shrinks to a quarter.
        let limit = maxChain;
        while (cand >= 0 && chain < limit) {
          const d = i - cand;
          if (d > WSIZE) break;
          if (bestLen >= goodMatch && limit === maxChain) limit = Math.max(32, maxChain >> 2);
          const isNear = d <= NEAR_DIST, isMid = d <= MID_DIST;
          if (data[cand + bestLen] === data[i + bestLen] ||
              (isNear && data[cand + nearLen] === data[i + nearLen]) ||
              (isMid && data[cand + midLen] === data[i + midLen])) {
            let l = 0;
            while (l < maxL && data[cand + l] === data[i + l]) l++;
            if (l > bestLen) { bestLen = l; bestDist = d; }
            if (isMid && l > midLen) { midLen = l; midDist = d; }
            if (isNear && l > nearLen) { nearLen = l; nearDist = d; }
          }
          cand = prev[cand];
          chain++;
        }
        prev[i] = head[h];
        head[h] = i;
      } else {
        const h = hash3(data, i);
        prev[i] = head[h];
        head[h] = i;
      }
    }
    lens[i] = bestLen >= MIN_MATCH ? bestLen : 0;
    dists[i] = bestLen >= MIN_MATCH ? bestDist : 0;
    nearLens[i] = nearLen >= MIN_MATCH ? nearLen : 0;
    nearDists[i] = nearLen >= MIN_MATCH ? nearDist : 0;
    midLens[i] = midLen >= MIN_MATCH ? midLen : 0;
    midDists[i] = midLen >= MIN_MATCH ? midDist : 0;
    prevLen = bestLen; prevDist = bestDist;
    prevNearLen = nearLen; prevNearDist = nearDist;
    prevMidLen = midLen; prevMidDist = midDist;
  }
  return { lens, dists, nearLens, nearDists, midLens, midDists };
}

/**
 * Cheapest tokenisation under litLen/distLen. Integer bit costs.
 * Returns {starts, isMatch, value, dist, count} — starts[k] is the data
 * offset where token k begins.
 */
function optimalParse(data, m, litLen, distLen, tiers = 3) {
  const n = data.length;
  const INF = 1e9;
  const dp = new Int32Array(n + 1).fill(INF);
  dp[0] = 0;
  const mlen = new Uint16Array(n + 1);
  const mdist = new Uint16Array(n + 1);
  const { lens, dists, nearLens, nearDists, midLens, midDists } = m;
  // lenCost[c] = bits of the length symbol for code c (without extra bits).
  const lenCost = new Int32Array(29);
  for (let c = 0; c < 29; c++) lenCost[c] = litLen[257 + c] + LEN_EXTRA[c];
  for (let i = 0; i < n; i++) {
    const base = dp[i];
    if (base === INF) continue;
    const litCost = base + litLen[data[i]];
    if (litCost < dp[i + 1]) { dp[i + 1] = litCost; mlen[i + 1] = 0; }
    const L = lens[i];
    if (L >= MIN_MATCH) {
      const dcost = distLen[DIST_CODE_OF[dists[i]]] + DIST_EXT_OF[dists[i]];
      const o0 = OFFER_OFF[L], o1 = OFFER_OFF[L + 1];
      for (let o = o0; o < o1; o++) {
        const l = OFFER[o];
        const cost = base + lenCost[LEN_CODE_OF[l]] + dcost;
        const j = i + l;
        if (cost < dp[j]) { dp[j] = cost; mlen[j] = l; mdist[j] = dists[i]; }
      }
    }
    const nL = nearLens[i];
    if (nL >= MIN_MATCH && (nL !== L || nearDists[i] !== dists[i])) {
      const dcost = distLen[DIST_CODE_OF[nearDists[i]]] + DIST_EXT_OF[nearDists[i]];
      const o0 = OFFER_OFF[nL], o1 = OFFER_OFF[nL + 1];
      for (let o = o0; o < o1; o++) {
        const l = OFFER[o];
        const cost = base + lenCost[LEN_CODE_OF[l]] + dcost;
        const j = i + l;
        if (cost < dp[j]) { dp[j] = cost; mlen[j] = l; mdist[j] = nearDists[i]; }
      }
    }
    const mL = midLens[i];
    if (tiers >= 3 && mL >= MIN_MATCH && (mL !== L || midDists[i] !== dists[i]) &&
        !(nL >= MIN_MATCH && mL === nL && midDists[i] === nearDists[i])) {
      const dcost = distLen[DIST_CODE_OF[midDists[i]]] + DIST_EXT_OF[midDists[i]];
      const o0 = OFFER_OFF[mL], o1 = OFFER_OFF[mL + 1];
      for (let o = o0; o < o1; o++) {
        const l = OFFER[o];
        const cost = base + lenCost[LEN_CODE_OF[l]] + dcost;
        const j = i + l;
        if (cost < dp[j]) { dp[j] = cost; mlen[j] = l; mdist[j] = midDists[i]; }
      }
    }
  }
  const starts = [], isMatch = [], value = [], dist = [];
  let i = n;
  while (i > 0) {
    const l = mlen[i];
    if (l === 0) { starts.push(i - 1); isMatch.push(0); value.push(data[i - 1]); dist.push(0); i -= 1; }
    else { starts.push(i - l); isMatch.push(1); value.push(l); dist.push(mdist[i]); i -= l; }
  }
  starts.reverse(); isMatch.reverse(); value.reverse(); dist.reverse();
  return {
    starts: Int32Array.from(starts),
    isMatch: Uint8Array.from(isMatch),
    value: Uint16Array.from(value),
    dist: Uint16Array.from(dist),
    count: starts.length,
  };
}

function tokenFrequencies(tokens, from, to) {
  const litFreq = new Int32Array(286);
  const distFreq = new Int32Array(30);
  for (let k = from; k < to; k++) {
    if (tokens.isMatch[k]) {
      litFreq[257 + LEN_CODE_OF[tokens.value[k]]]++;
      distFreq[DIST_CODE_OF[tokens.dist[k]]]++;
    } else litFreq[tokens.value[k]]++;
  }
  litFreq[256]++;
  return { litFreq, distFreq };
}

const CL_ORDER = [16, 17, 18, 0, 8, 7, 9, 6, 10, 5, 11, 4, 12, 3, 13, 2, 14, 1, 15];

/** Emit one block's tokens; `fixed` uses fixed Huffman codes. */
function emitBlock(writer, tokens, from, to, litLen, distLen, fixed) {
  const ll = fixed ? FIXED_LIT_LEN : litLen;
  const dl = fixed ? FIXED_DIST_LEN : distLen;
  if (!fixed) {
    let hlit = 257;
    for (let s = 285; s >= 257; s--) if (litLen[s] > 0) { hlit = s + 1; break; }
    let hdist = 1;
    for (let s = 29; s >= 0; s--) if (distLen[s] > 0) { hdist = s + 1; break; }
    const seq = new Int32Array(hlit + hdist);
    for (let s = 0; s < hlit; s++) seq[s] = litLen[s];
    for (let s = 0; s < hdist; s++) seq[hlit + s] = distLen[s];
    const clSyms = [], clExtra = [];
    let i = 0;
    while (i < seq.length) {
      const v = seq[i];
      if (v === 0) {
        let run = 0;
        while (i + run < seq.length && seq[i + run] === 0) run++;
        i += run;
        while (run >= 11) { const take = Math.min(run, 138); clSyms.push(18); clExtra.push(take - 11); run -= take; }
        if (run >= 3) { clSyms.push(17); clExtra.push(run - 3); run = 0; }
        while (run > 0) { clSyms.push(0); clExtra.push(0); run--; }
      } else {
        clSyms.push(v); clExtra.push(0); i++;
        let run = 0;
        while (i + run < seq.length && seq[i + run] === v) run++;
        let left = run;
        while (left >= 3) { const take = Math.min(left, 6); clSyms.push(16); clExtra.push(take - 3); left -= take; }
        for (let r = 0; r < left; r++) { clSyms.push(v); clExtra.push(0); }
        i += run;
      }
    }
    const clFreq = new Int32Array(19);
    for (const s of clSyms) clFreq[s]++;
    let clUsed = 0;
    for (let s = 0; s < 19; s++) if (clFreq[s] > 0) clUsed++;
    if (clUsed < 2) return false;
    const clLen = buildLengths(clFreq, 7);
    let hclen = 4;
    for (let k = 18; k >= 4; k--) if (clLen[CL_ORDER[k]] > 0) { hclen = k + 1; break; }
    var litCode = canonicalCodes(ll), distCode = canonicalCodes(dl);
    var clCode = canonicalCodes(clLen);
    writer.writeBits(2, 2);
    writer.writeBits(hlit - 257, 5);
    writer.writeBits(hdist - 1, 5);
    writer.writeBits(hclen - 4, 4);
    for (let k = 0; k < hclen; k++) writer.writeBits(clLen[CL_ORDER[k]], 3);
    for (let k = 0; k < clSyms.length; k++) {
      const s = clSyms[k];
      writer.writeBits(reverseBits(clCode[s], clLen[s]), clLen[s]);
      if (s === 16) writer.writeBits(clExtra[k], 2);
      else if (s === 17) writer.writeBits(clExtra[k], 3);
      else if (s === 18) writer.writeBits(clExtra[k], 7);
    }
  } else {
    var litCode = canonicalCodes(ll), distCode = canonicalCodes(dl);
    writer.writeBits(1, 2);
  }
  for (let k = from; k < to; k++) {
    if (tokens.isMatch[k]) {
      const l = tokens.value[k], lc = LEN_CODE_OF[l];
      writer.writeBits(reverseBits(litCode[257 + lc], ll[257 + lc]), ll[257 + lc]);
      writer.writeBits(l - LEN_BASE[lc], LEN_EXTRA[lc]);
      const d = tokens.dist[k], dc = DIST_CODE_OF[d];
      writer.writeBits(reverseBits(distCode[dc], dl[dc]), dl[dc]);
      writer.writeBits(d - DIST_BASE[dc], DIST_EXTRA[dc]);
    } else {
      const b = tokens.value[k];
      writer.writeBits(reverseBits(litCode[b], ll[b]), ll[b]);
    }
  }
  writer.writeBits(reverseBits(litCode[256], ll[256]), ll[256]);
  return true;
}

/**
 * Split token ranges at data offsets `bounds` (sorted, within (0, n)),
 * emitting one block per range. Returns the deflate bytes (no zlib wrapper)
 * or null. `bounds` are data offsets; each block starts at the first token
 * starting at or after its bound.
 */
function emitSplit(tokens, n, bounds) {
  const cuts = [0];
  for (const b of bounds) {
    let lo = 0, hi = tokens.count;
    while (lo < hi) { const mid = (lo + hi) >> 1; if (tokens.starts[mid] < b) lo = mid + 1; else hi = mid; }
    if (lo > cuts[cuts.length - 1] && lo < tokens.count) cuts.push(lo);
  }
  cuts.push(tokens.count);
  const writer = new BitWriter(2 * n + 8192);
  for (let b = 0; b < cuts.length - 1; b++) {
    const from = cuts[b], to = cuts[b + 1];
    if (from >= to) continue;
    const isLast = b === cuts.length - 2;
    const { litFreq, distFreq } = tokenFrequencies(tokens, from, to);
    let distUsed = 0;
    for (let s = 0; s < 30; s++) if (distFreq[s] > 0) distUsed++;
    if (distUsed === 0) distFreq[0] = 1;
    else if (distUsed === 1 && distFreq[0] === 0) distFreq[0] = 1;
    else if (distUsed === 1) distFreq[1] = 1;
    const litLen = buildLengths(litFreq, 15);
    const distLen = buildLengths(distFreq, 15);
    // Fixed vs dynamic: estimate dynamic bits cheaply from frequencies.
    let dynBits = 0;
    for (let s = 0; s < 286; s++) if (litFreq[s] > 0) dynBits += litFreq[s] * litLen[s];
    for (let s = 0; s < 30; s++) if (distFreq[s] > 0) dynBits += distFreq[s] * distLen[s];
    let fixBits = 0;
    for (let s = 0; s < 286; s++) if (litFreq[s] > 0) fixBits += litFreq[s] * FIXED_LIT_LEN[s];
    for (let s = 0; s < 30; s++) if (distFreq[s] > 0) fixBits += distFreq[s] * FIXED_DIST_LEN[s];
    writer.writeBits(isLast ? 1 : 0, 1);
    if (fixBits < dynBits) {
      if (!emitBlock(writer, tokens, from, to, null, null, true)) return null;
    } else {
      if (!emitBlock(writer, tokens, from, to, litLen, distLen, false)) return null;
    }
  }
  return writer.finish();
}

export function optimalDeflate2(data, rowLen, opts = {}) {
  const n = data.length;
  if (n === 0) return null;
  const maxChain = opts.maxChain ?? 256;
  const goodMatch = opts.goodMatch ?? 32;
  const passes = opts.passes ?? 2;
  const t0 = Date.now();
  const m = findMatches(data, rowLen, maxChain, goodMatch, opts.structGate ?? 128);
  const tMatch = Date.now() - t0;
  let litLen = FIXED_LIT_LEN, distLen = FIXED_DIST_LEN, tokens = null;
  let tParse = 0;
  for (let p = 0; p < passes; p++) {
    const tp = Date.now();
    tokens = optimalParse(data, m, litLen, distLen, opts.tiers ?? 3);
    tParse += Date.now() - tp;
    const { litFreq, distFreq } = tokenFrequencies(tokens, 0, tokens.count);
    litLen = buildLengths(litFreq, 15);
    distLen = buildLengths(distFreq, 15);
  }
  // Candidate split granularities (rows per block); 0 = whole stream.
  const rows = Math.floor(n / rowLen);
  const cands = [0, 240, 120, 60, 30];
  let best = null;
  const tEmit0 = Date.now();
  for (const g of cands) {
    if (g === 0) {
      const deflated = emitSplit(tokens, n, []);
      if (deflated !== null && (best === null || deflated.length < best.length)) best = deflated;
    } else {
      const bounds = [];
      for (let r = g; r < rows; r += g) bounds.push(r * rowLen);
      const deflated = emitSplit(tokens, n, bounds);
      if (deflated !== null && (best === null || deflated.length < best.length)) best = deflated;
    }
  }
  const tEmit = Date.now() - tEmit0;
  if (best === null) return null;
  const out = new Uint8Array(2 + best.length + 4);
  out[0] = 0x78; out[1] = 0x9c;
  out.set(best, 2);
  new DataView(out.buffer).setUint32(2 + best.length, adler32(data));
  if (opts.timings) opts.timings.match = tMatch, opts.timings.parse = tParse, opts.timings.emit = tEmit;
  return out;
}
