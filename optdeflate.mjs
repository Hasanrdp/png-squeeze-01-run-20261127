// Optimal-parse DEFLATE for the PNG squeezer: a zopfli-style encoder written
// for this entry. It takes the filtered bytes of one image and returns one
// zlib stream holding a single dynamic-Huffman block, or null when it cannot
// (the caller then keeps zlib's own stream, which is always valid).
//
// The parse is a shortest path over the byte stream: at each position the
// choice is a literal or a match, priced by the code lengths of the current
// Huffman tables, with lengths tried only at the longest value of each
// length code (a longer length at the same code price always wins). Match
// candidates come from 3-byte hash chains with a previous-match extension,
// so flat runs stay cheap. Two passes refine the tables: the first prices
// with the fixed Huffman lengths, the second with dynamic lengths built from
// the first pass's tokens, and the block is written with lengths rebuilt from
// the second pass. Everything is deterministic: fixed chain limits, fixed
// iteration counts, no clock.

const MIN_MATCH = 3;
const MAX_MATCH = 258;
const WSIZE = 32768;
const HASH_BITS = 16;
const HASH_SIZE = 1 << HASH_BITS;
const HASH_MASK = HASH_SIZE - 1;
const MAX_CHAIN = 256;
const GOOD_MATCH = 64;
// A "near" match is one whose distance is at most this. Distance codes are
// far cheaper for near matches, so the parser keeps the longest near match
// as a second option alongside the longest match overall: the longest match
// is often far away, while a nearly-as-long near one costs fewer bits.
const NEAR_DIST = 256;
const MID_DIST = 2048;

// DEFLATE's length codes: base length and extra bits per code (29 codes, 257..285).
const LEN_BASE = [3, 4, 5, 6, 7, 8, 9, 10, 11, 13, 15, 17, 19, 23, 27, 31, 35, 43, 51, 59, 67, 83, 99, 115, 131, 163, 195, 227, 258];
const LEN_EXTRA = [0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 2, 2, 2, 2, 3, 3, 3, 3, 4, 4, 4, 4, 5, 5, 5, 5, 0];
// DEFLATE's distance codes: base distance and extra bits per code (30 codes, 0..29).
const DIST_BASE = [1, 2, 3, 4, 5, 7, 9, 13, 17, 25, 33, 49, 65, 97, 129, 193, 257, 385, 513, 769, 1025, 1537, 2049, 3073, 4097, 6145, 8193, 12289, 16385, 24577];
const DIST_EXTRA = [0, 0, 0, 0, 1, 1, 2, 2, 3, 3, 4, 4, 5, 5, 6, 6, 7, 7, 8, 8, 9, 9, 10, 10, 11, 11, 12, 12, 13, 13];

// Length code index and extra bits for every length 3..258.
const LEN_CODE_OF = new Int32Array(259);
const LEN_EXT_OF = new Int32Array(259);
for (let c = 0; c < 29; c++) {
  const hi = c === 28 ? 258 : LEN_BASE[c + 1] - 1;
  for (let l = LEN_BASE[c]; l <= hi; l++) {
    LEN_CODE_OF[l] = c;
    LEN_EXT_OF[l] = LEN_EXTRA[c];
  }
}
// Distance code index and extra bits for every distance 1..32768.
const DIST_CODE_OF = new Int32Array(WSIZE + 1);
const DIST_EXT_OF = new Int32Array(WSIZE + 1);
for (let c = 0; c < 30; c++) {
  const hi = c === 29 ? WSIZE : DIST_BASE[c + 1] - 1;
  for (let d = DIST_BASE[c]; d <= hi; d++) {
    DIST_CODE_OF[d] = c;
    DIST_EXT_OF[d] = DIST_EXTRA[c];
  }
}

// The fixed Huffman code lengths (RFC 1951) used to price the first pass.
const FIXED_LIT_LEN = new Int32Array(286);
for (let s = 0; s < 286; s++) FIXED_LIT_LEN[s] = s < 144 ? 8 : s < 256 ? 9 : s < 280 ? 7 : 8;
const FIXED_DIST_LEN = new Int32Array(30).fill(5);

/** Adler-32 of bytes, the checksum a zlib stream ends with. */
function adler32(data) {
  let a = 1;
  let b = 0;
  for (let i = 0; i < data.length; ) {
    const end = Math.min(data.length, i + 5552);
    for (; i < end; i++) {
      a += data[i];
      b += a;
    }
    a %= 65521;
    b %= 65521;
  }
  return ((b << 16) | a) >>> 0;
}

/** A bit writer: bits go out least-significant-bit first, as DEFLATE wants. */
class BitWriter {
  constructor(capacity) {
    this.out = new Uint8Array(capacity);
    this.at = 0;
    this.bitbuf = 0;
    this.bitcnt = 0;
  }
  writeBits(value, count) {
    this.bitbuf |= value << this.bitcnt;
    this.bitcnt += count;
    while (this.bitcnt >= 8) {
      this.out[this.at++] = this.bitbuf & 0xff;
      this.bitbuf >>>= 8;
      this.bitcnt -= 8;
    }
  }
  writeCode(code, length) {
    this.writeBits(code, length);
  }
  finish() {
    if (this.bitcnt > 0) {
      this.out[this.at++] = this.bitbuf & 0xff;
      this.bitbuf = 0;
      this.bitcnt = 0;
    }
    return this.out.subarray(0, this.at);
  }
}

/**
 * Huffman code lengths for an alphabet from symbol frequencies, capped at
 * `maxBits`. A heap builds the tree (ties break by symbol, so the result is
 * deterministic); lengths over the cap are pulled back with the standard
 * overflow redistribution, then reassigned shortest-first by frequency.
 * Returns an Int32Array of lengths, 0 for unused symbols.
 */
function buildLengths(freq, maxBits) {
  const n = freq.length;
  const lengths = new Int32Array(n);
  const used = [];
  for (let s = 0; s < n; s++) if (freq[s] > 0) used.push(s);
  if (used.length === 0) return lengths;
  if (used.length === 1) {
    lengths[used[0]] = 1;
    return lengths;
  }
  // Heap of tree nodes, smallest frequency first; ties break by node id so
  // the shape is deterministic. Leaves are symbols; inner nodes get ids >= n.
  const heapFreq = [];
  const heapId = [];
  const nodeFreq = new Float64Array(2 * n);
  const nodeLeft = new Int32Array(2 * n).fill(-1);
  const nodeRight = new Int32Array(2 * n).fill(-1);
  const nodeDepth = new Int32Array(2 * n);
  let nodes = 0;
  const heapPush = (f, id) => {
    heapFreq.push(f);
    heapId.push(id);
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
    const topF = heapFreq[0];
    const topId = heapId[0];
    const lastF = heapFreq.pop();
    const lastId = heapId.pop();
    if (heapFreq.length > 0) {
      heapFreq[0] = lastF;
      heapId[0] = lastId;
      let i = 0;
      for (;;) {
        const l = i * 2 + 1;
        const r = l + 1;
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
  for (const s of used) {
    nodeFreq[nodes] = freq[s];
    heapPush(freq[s], nodes);
    nodes++;
  }
  // Inner nodes take ids from n upward; leaves keep their symbol as id.
  let nextId = n;
  const idOfLeaf = new Map();
  for (let k = 0; k < used.length; k++) idOfLeaf.set(used[k], k);
  // Rebuild: leaf node ids are 0..used-1 in the order pushed; map them back.
  const leafNodeOf = new Int32Array(n).fill(-1);
  for (let k = 0; k < used.length; k++) leafNodeOf[used[k]] = k;
  while (heapFreq.length > 1) {
    const [f1, id1] = heapPop();
    const [f2, id2] = heapPop();
    nodeFreq[nextId] = f1 + f2;
    nodeLeft[nextId] = id1;
    nodeRight[nextId] = id2;
    heapPush(f1 + f2, nextId);
    nextId++;
  }
  const root = heapId[0];
  // Depths by walking down from the root.
  const stack = [[root, 0]];
  const depthOf = new Int32Array(nextId);
  while (stack.length > 0) {
    const [id, d] = stack.pop();
    depthOf[id] = d;
    if (nodeLeft[id] !== -1) {
      stack.push([nodeLeft[id], d + 1]);
      stack.push([nodeRight[id], d + 1]);
    }
  }
  // Count lengths, folding the over-long into the cap as overflow.
  const blCount = new Int32Array(maxBits + 1);
  let overflow = 0;
  for (const s of used) {
    const d = depthOf[leafNodeOf[s]];
    if (d > maxBits) {
      overflow++;
      blCount[maxBits]++;
    } else {
      blCount[d]++;
    }
  }
  // Pull the over-subscribed count back to a complete code (Kraft sum 1).
  // Capping the over-long leaves at maxBits overshoots the Kraft sum by E
  // units of 2^-maxBits; each step below removes exactly one such unit (a
  // leaf moves one level down, its place at the cap taken by the overflow
  // leaf's brother), so E steps land exactly on a complete code.
  if (overflow > 0) {
    let excess = 0;
    for (let b = 1; b <= maxBits; b++) excess += blCount[b] * (1 << (maxBits - b));
    excess -= 1 << maxBits;
    while (excess > 0) {
      let m = maxBits - 1;
      while (blCount[m] === 0) m--;
      blCount[m]--;
      blCount[m + 1] += 2;
      blCount[maxBits]--;
      excess--;
    }
  }
  // Reassign: most frequent symbols take the shortest lengths.
  const byFreq = [...used].sort((a, b) => freq[b] - freq[a] || a - b);
  let k = 0;
  for (let b = 1; b <= maxBits; b++) {
    for (let j = 0; j < blCount[b]; j++) lengths[byFreq[k++]] = b;
  }
  return lengths;
}

/** Canonical Huffman codes from code lengths: codes[s] is the code, lengths[s] its bits. */
function canonicalCodes(lengths) {
  const n = lengths.length;
  const codes = new Int32Array(n);
  const count = new Int32Array(16);
  for (let s = 0; s < n; s++) if (lengths[s] > 0) count[lengths[s]]++;
  const next = new Int32Array(16);
  let code = 0;
  for (let b = 1; b < 16; b++) {
    code = (code + count[b - 1]) << 1;
    next[b] = code;
  }
  for (let s = 0; s < n; s++) {
    const len = lengths[s];
    if (len > 0) codes[s] = next[len]++;
  }
  return codes;
}

/** Huffman codes in DEFLATE's bit order: the code's bits are reversed before writing. */
function reverseBits(code, length) {
  let r = 0;
  for (let i = 0; i < length; i++) {
    r = (r << 1) | (code & 1);
    code >>>= 1;
  }
  return r;
}

// ---------------------------------------------------------------------------
// LZ77 match finding: 4-byte hash chains over a 32 KiB window.
// ---------------------------------------------------------------------------

// A 4-byte hash: the filtered screenshot bytes are mostly 0/1, so a 3-byte
// hash collapses into a few buckets with chains thousands long, and a
// 128-entry walk never reaches the far candidates that hold the long
// matches. Four bytes spread the chains out, so the same walk covers far
// more distance. Length-3 matches are given up (they are marginal: zlib
// uses none on this data).
function hash4(data, i) {
  const v = (data[i] << 24) ^ (data[i + 1] << 16) ^ (data[i + 2] << 8) ^ data[i + 3];
  return (Math.imul(v, 2654435761) >>> 16) & HASH_MASK;
}

/**
 * The longest match at every position, in three distance tiers: lens[i] /
 * dists[i] the longest overall, nearLens[i] / nearDists[i] the longest with
 * distance at most NEAR_DIST, midLens[i] / midDists[i] the longest with
 * distance at most MID_DIST (0 when a tier has no match of length 3+).
 * Distance codes are far cheaper for near matches, so the parser tries all
 * three: the longest match is often far away, while a nearly-as-long near
 * one costs fewer bits. A position reuses the matches found one byte
 * earlier (same distances, one shorter) before walking its hash chain,
 * which keeps flat runs cheap; the chain walk stops after MAX_CHAIN
 * candidates or at a match of GOOD_MATCH. When a tier array is not
 * supplied it is still tracked internally so the other tiers are unaffected.
 */
function findMatches(data, lens, dists, nearLens = null, nearDists = null, midLens = null, midDists = null) {
  const n = data.length;
  const head = new Int32Array(HASH_SIZE).fill(-1);
  const prev = new Int32Array(n).fill(-1);
  const nl = nearLens || new Uint16Array(n);
  const nd = nearDists || new Uint16Array(n);
  const ml = midLens || new Uint16Array(n);
  const md = midDists || new Uint16Array(n);
  let prevLen = 0, prevDist = 0;
  let prevNearLen = 0, prevNearDist = 0;
  let prevMidLen = 0, prevMidDist = 0;
  for (let i = 0; i < n; i++) {
    let bestLen = 0, bestDist = 0;
    let nearLen = 0, nearDist = 0;
    let midLen = 0, midDist = 0;
    // Four bytes must remain to hash this position; the last three bytes
    // can only ever start a length-3 match, which is not worth tracking.
    if (i + 4 <= n) {
      const maxL = Math.min(MAX_MATCH, n - i);
      // Extend the matches found at i - 1: same distances, one byte
      // shorter. A match also seeds every tier its distance qualifies for.
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
      if ((bestLen < GOOD_MATCH || nearLen < GOOD_MATCH || midLen < GOOD_MATCH) && bestLen < maxL) {
        const h = hash4(data, i);
        let cand = head[h];
        let chain = 0;
        while (cand >= 0 && chain < MAX_CHAIN) {
          const d = i - cand;
          // The window is 32 KiB: older candidates are out of reach, and
          // the chain only walks further back, so stop here.
          if (d > WSIZE) break;
          // Once every tier is good enough, stop; and once the best is
          // good and the walk has passed MID_DIST, no tier candidate can
          // remain (all tiers end at MID_DIST), so stop too.
          if (bestLen >= GOOD_MATCH && nearLen >= GOOD_MATCH && midLen >= GOOD_MATCH) break;
          if (bestLen >= GOOD_MATCH && d > MID_DIST) break;
          const isNear = d <= NEAR_DIST;
          const isMid = d <= MID_DIST;
          // A candidate can only beat a tier when its byte at that tier's
          // best length matches.
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
        const h = hash4(data, i);
        prev[i] = head[h];
        head[h] = i;
      }
    }
    lens[i] = bestLen >= MIN_MATCH ? bestLen : 0;
    dists[i] = bestLen >= MIN_MATCH ? bestDist : 0;
    nl[i] = nearLen >= MIN_MATCH ? nearLen : 0;
    nd[i] = nearLen >= MIN_MATCH ? nearDist : 0;
    ml[i] = midLen >= MIN_MATCH ? midLen : 0;
    md[i] = midLen >= MIN_MATCH ? midDist : 0;
    prevLen = bestLen; prevDist = bestDist;
    prevNearLen = nearLen; prevNearDist = nearDist;
    prevMidLen = midLen; prevMidDist = midDist;
  }
}

// ---------------------------------------------------------------------------
// Optimal parsing: shortest path over literals and matches.
// ---------------------------------------------------------------------------

/**
 * The cheapest tokenisation of `data` under `litLen`/`distLen` code lengths.
 * Returns the tokens as parallel arrays: isMatch, length (match) or byte
 * (literal), distance. Only the longest length of each length code is tried,
 * since a longer length at the same code price always wins.
 */
function optimalParse(data, lens, dists, litLen, distLen, nearLens = null, nearDists = null, midLens = null, midDists = null) {
  const n = data.length;
  const dp = new Float64Array(n + 1).fill(Infinity);
  dp[0] = 0;
  const mlen = new Uint16Array(n + 1);
  const mdist = new Uint16Array(n + 1);
  // Offer one match at position i to the shortest path: the longest length
  // of each length code at that distance, since a longer length at the same
  // code price always wins.
  const offer = (i, base, L, d) => {
    const dcost = distLen[DIST_CODE_OF[d]] + DIST_EXT_OF[d];
    for (let c = 0; c < 29; c++) {
      const lo = LEN_BASE[c];
      if (lo > L) break;
      const hi = c === 28 ? MAX_MATCH : LEN_BASE[c + 1] - 1;
      const l = Math.min(hi, L);
      const cost = base + litLen[257 + c] + LEN_EXTRA[c] + dcost;
      const j = i + l;
      if (cost < dp[j]) {
        dp[j] = cost;
        mlen[j] = l;
        mdist[j] = d;
      }
    }
  };
  for (let i = 0; i < n; i++) {
    const base = dp[i];
    if (base === Infinity) continue;
    const litCost = base + litLen[data[i]];
    if (litCost < dp[i + 1]) {
      dp[i + 1] = litCost;
      mlen[i + 1] = 0;
    }
    // Try the longest match and, when they differ, the longest near and
    // mid matches: a slightly shorter near match often costs fewer bits.
    const L = lens[i];
    if (L >= MIN_MATCH) offer(i, base, L, dists[i]);
    if (nearLens) {
      const nL = nearLens[i];
      const nD = nearDists[i];
      if (nL >= MIN_MATCH && (nL !== L || nD !== dists[i])) offer(i, base, nL, nD);
    }
    if (midLens) {
      const mL = midLens[i];
      const mD = midDists[i];
      if (mL >= MIN_MATCH && (mL !== L || mD !== dists[i]) &&
          !(nearLens && mL === nearLens[i] && mD === nearDists[i])) {
        offer(i, base, mL, mD);
      }
    }
  }
  // Walk back from the end, collecting tokens in reverse, then flip them.
  const isMatch = [];
  const value = [];
  const dist = [];
  let i = n;
  while (i > 0) {
    const l = mlen[i];
    if (l === 0) {
      isMatch.push(0);
      value.push(data[i - 1]);
      dist.push(0);
      i -= 1;
    } else {
      isMatch.push(1);
      value.push(l);
      dist.push(mdist[i]);
      i -= l;
    }
  }
  isMatch.reverse();
  value.reverse();
  dist.reverse();
  return { isMatch: Uint8Array.from(isMatch), value: Uint16Array.from(value), dist: Uint16Array.from(dist), count: isMatch.length };
}

// ---------------------------------------------------------------------------
// Writing the dynamic-Huffman block.
// ---------------------------------------------------------------------------

/** Literal/length and distance frequencies of a token list (end-of-block included). */
function tokenFrequencies(tokens) {
  const litFreq = new Int32Array(286);
  const distFreq = new Int32Array(30);
  for (let k = 0; k < tokens.count; k++) {
    if (tokens.isMatch[k]) {
      litFreq[257 + LEN_CODE_OF[tokens.value[k]]]++;
      distFreq[DIST_CODE_OF[tokens.dist[k]]]++;
    } else {
      litFreq[tokens.value[k]]++;
    }
  }
  litFreq[256]++;
  return { litFreq, distFreq };
}

/** The order the code-length code's lengths are written in. */
const CL_ORDER = [16, 17, 18, 0, 8, 7, 9, 6, 10, 5, 11, 4, 12, 3, 13, 2, 14, 1, 15];

/**
 * One dynamic-Huffman block holding `tokens`, as a Uint8Array of deflate
 * bytes (no zlib wrapper). Returns null when the code-length code would be
 * degenerate (a single symbol), which the caller treats as "use zlib".
 */
function emitBlock(tokens, litLen, distLen) {
  let hlit = 257;
  for (let s = 285; s >= 257; s--) {
    if (litLen[s] > 0) {
      hlit = s + 1;
      break;
    }
  }
  let hdist = 1;
  for (let s = 29; s >= 0; s--) {
    if (distLen[s] > 0) {
      hdist = s + 1;
      break;
    }
  }
  const seq = new Int32Array(hlit + hdist);
  for (let s = 0; s < hlit; s++) seq[s] = litLen[s];
  for (let s = 0; s < hdist; s++) seq[hlit + s] = distLen[s];
  // Run-length encode the length sequence with codes 16/17/18.
  const clSyms = [];
  const clExtra = [];
  let i = 0;
  while (i < seq.length) {
    const v = seq[i];
    if (v === 0) {
      let run = 0;
      while (i + run < seq.length && seq[i + run] === 0) run++;
      i += run;
      while (run >= 11) {
        const take = Math.min(run, 138);
        clSyms.push(18);
        clExtra.push(take - 11);
        run -= take;
      }
      if (run >= 3) {
        clSyms.push(17);
        clExtra.push(run - 3);
        run = 0;
      }
      while (run > 0) {
        clSyms.push(0);
        clExtra.push(0);
        run--;
      }
    } else {
      clSyms.push(v);
      clExtra.push(0);
      i++;
      let run = 0;
      while (i + run < seq.length && seq[i + run] === v) run++;
      let left = run;
      while (left >= 3) {
        const take = Math.min(left, 6);
        clSyms.push(16);
        clExtra.push(take - 3);
        left -= take;
      }
      for (let r = 0; r < left; r++) {
        clSyms.push(v);
        clExtra.push(0);
      }
      i += run;
    }
  }
  const clFreq = new Int32Array(19);
  for (const s of clSyms) clFreq[s]++;
  let clUsed = 0;
  for (let s = 0; s < 19; s++) if (clFreq[s] > 0) clUsed++;
  if (clUsed < 2) return null;
  const clLen = buildLengths(clFreq, 7);
  let hclen = 4;
  for (let k = 18; k >= 4; k--) {
    if (clLen[CL_ORDER[k]] > 0) {
      hclen = k + 1;
      break;
    }
  }
  const litCode = canonicalCodes(litLen);
  const distCode = canonicalCodes(distLen);
  const clCode = canonicalCodes(clLen);
  // At most 16 bits an input byte (a 3-byte match costs at most 48 bits).
  const writer = new BitWriter(2 * tokens.rawLength + 8192);
  writer.writeBits(1, 1);
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
  for (let k = 0; k < tokens.count; k++) {
    if (tokens.isMatch[k]) {
      const l = tokens.value[k];
      const lc = LEN_CODE_OF[l];
      writer.writeBits(reverseBits(litCode[257 + lc], litLen[257 + lc]), litLen[257 + lc]);
      writer.writeBits(l - LEN_BASE[lc], LEN_EXTRA[lc]);
      const d = tokens.dist[k];
      const dc = DIST_CODE_OF[d];
      writer.writeBits(reverseBits(distCode[dc], distLen[dc]), distLen[dc]);
      writer.writeBits(d - DIST_BASE[dc], DIST_EXTRA[dc]);
    } else {
      const b = tokens.value[k];
      writer.writeBits(reverseBits(litCode[b], litLen[b]), litLen[b]);
    }
  }
  writer.writeBits(reverseBits(litCode[256], litLen[256]), litLen[256]);
  return writer.finish();
}

/**
 * The optimal-parse zlib stream of `data`, or null when it cannot be built.
 * The caller compares its length with zlib's and ships the smaller.
 */
export function optimalDeflate(data) {
  const n = data.length;
  if (n === 0) return null;
  const lens = new Uint16Array(n);
  const dists = new Uint16Array(n);
  const nearLens = new Uint16Array(n);
  const nearDists = new Uint16Array(n);
  const midLens = new Uint16Array(n);
  const midDists = new Uint16Array(n);
  findMatches(data, lens, dists, nearLens, nearDists, midLens, midDists);
  // Price the parse, rebuild the tables from the tokens, and parse again:
  // each round's tables fit the previous round's tokens better, so the cost
  // falls until it settles. The first round prices with the fixed lengths.
  let litLen = FIXED_LIT_LEN;
  let distLen = FIXED_DIST_LEN;
  let tokens = null;
  for (let pass = 0; pass < 2; pass++) {
    tokens = optimalParse(data, lens, dists, litLen, distLen, nearLens, nearDists, midLens, midDists);
    const { litFreq, distFreq } = tokenFrequencies(tokens);
    litLen = buildLengths(litFreq, 15);
    distLen = buildLengths(distFreq, 15);
  }
  const { litFreq, distFreq } = tokenFrequencies(tokens);
  // The block needs a distance code even when no match was used; a dummy
  // count on symbol 0 gives it one, and a second symbol keeps the code from
  // being a single symbol when only one distance is ever used.
  let distUsed = 0;
  for (let s = 0; s < 30; s++) if (distFreq[s] > 0) distUsed++;
  if (distUsed === 0) distFreq[0] = 1;
  else if (distUsed === 1 && distFreq[0] === 0) distFreq[0] = 1;
  else if (distUsed === 1) distFreq[1] = 1;
  litLen = buildLengths(litFreq, 15);
  distLen = buildLengths(distFreq, 15);
  tokens.rawLength = n;
  const deflated = emitBlock(tokens, litLen, distLen);
  if (deflated === null) return null;
  const out = new Uint8Array(2 + deflated.length + 4);
  out[0] = 0x78;
  out[1] = 0x9c;
  out.set(deflated, 2);
  new DataView(out.buffer).setUint32(2 + deflated.length, adler32(data));
  return out;
}
