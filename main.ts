// SqueezeShot v2 — a lossless PNG re-encoder for make.fun's png-squeeze-01-run-20261127.
//
// One program answers a whole set: it reads each /input/<id>/image.png (a stored
// RGBA screenshot, 1280x720), and writes the same pixels back as the smallest PNG
// it can find, losslessly, as /output/<id>/image.png.
//
// How it squeezes:
//   * Colour reduction first. An image with at most 256 colours becomes a palette
//     image (type 3, transparent entries first so tRNS stays short); an all-grey
//     image becomes grey (type 0) or grey+alpha (type 4); an opaque image drops
//     its alpha channel (type 2). A single fully-transparent value is keyed with
//     tRNS instead of an alpha channel when the image allows it.
//   * Filter search second. For every candidate form it tries fixed filters,
//     the minimum-sum and fewest-pairs per-row heuristics, and a per-row brute
//     force that weighs each filter by a real level-4 deflate of the row against
//     the 32 KiB written before it. Each candidate is weighed by a level-6 zlib
//     run of its filtered bytes plus its PLTE/tRNS chunk cost.
//   * Deflate last. The winning filtered stream is re-compressed four ways and
//     the smallest ships: zlib level 9 (default and filtered strategies), zlib
//     level 9 with the stream split into fresh-Huffman blocks at row
//     boundaries, and the optimal-parse encoder in deflate.mjs (3-byte hash
//     chains with structural row/run candidates, an exact-bit shortest-path
//     parse in three refinement passes, and token-level block splitting).
//     Every non-zlib candidate is verified by inflating it back before it
//     is trusted.
//
// Everything is deterministic: no clock, no randomness, no environment input.
// Node 22 runs this file as node /bot/main.ts; it uses only node: built-ins.
import { inflateSync, deflateSync, createDeflate, constants } from 'node:zlib';
import { mkdirSync, readdirSync, readFileSync, writeFileSync } from 'node:fs';
import { join } from 'node:path';
import { optimalDeflate2 } from './deflate.mjs';

const IN_DIR = process.env.MAKEFUN_INPUT_DIR ?? '/input';
const OUT_DIR = process.env.MAKEFUN_OUTPUT_DIR ?? '/output';

// ---------------------------------------------------------------------------
// PNG chunks: CRC-32, writer, and a decoder for the PNGs the contest reads.
// ---------------------------------------------------------------------------

const PNG_SIG = Uint8Array.of(137, 80, 78, 71, 13, 10, 26, 10);

const CRC_TABLE = (() => {
  const table = new Int32Array(256);
  for (let n = 0; n < 256; n++) {
    let c = n;
    for (let k = 0; k < 8; k++) c = c & 1 ? 0xedb88320 ^ (c >>> 1) : c >>> 1;
    table[n] = c;
  }
  return table;
})();

function crc32(bytes, start, end) {
  let c = -1;
  for (let i = start; i < end; i++) c = CRC_TABLE[(c ^ bytes[i]) & 0xff] ^ (c >>> 8);
  return (c ^ -1) >>> 0;
}

function chunkBytes(type, data) {
  const out = new Uint8Array(12 + data.length);
  const view = new DataView(out.buffer);
  view.setUint32(0, data.length);
  for (let i = 0; i < 4; i++) out[4 + i] = type.charCodeAt(i);
  out.set(data, 8);
  view.setUint32(8 + data.length, crc32(out, 4, 8 + data.length));
  return out;
}

function pngFile(chunks) {
  let size = PNG_SIG.length;
  for (const [, data] of chunks) size += 12 + data.length;
  const out = new Uint8Array(size);
  out.set(PNG_SIG, 0);
  let at = PNG_SIG.length;
  for (const [type, data] of chunks) {
    out.set(chunkBytes(type, data), at);
    at += 12 + data.length;
  }
  return out;
}

function ihdrData(width, height, colourType) {
  const data = new Uint8Array(13);
  const view = new DataView(data.buffer);
  view.setUint32(0, width);
  view.setUint32(4, height);
  data[8] = 8;
  data[9] = colourType;
  return data;
}

const CHANNELS = { 0: 1, 2: 3, 3: 1, 4: 2, 6: 4 };
const READABLE_CHUNKS = ['IHDR', 'PLTE', 'tRNS', 'IDAT', 'IEND'];

/** The Paeth predictor shared by filter 4 and its inverse. */
function paethPredictor(a, b, c) {
  const p = a + b - c;
  const pa = Math.abs(p - a);
  const pb = Math.abs(p - b);
  const pc = Math.abs(p - c);
  if (pa <= pb && pa <= pc) return a;
  return pb <= pc ? b : c;
}

/**
 * Decode a PNG the contest reads into RGBA pixels (4 bytes a pixel, rows top
 * to bottom). Throws when the file is not one the contest reads.
 */
function decodePng(bytes) {
  if (bytes.length < PNG_SIG.length || PNG_SIG.some((b, i) => bytes[i] !== b)) {
    throw new Error('not a PNG');
  }
  const view = new DataView(bytes.buffer, bytes.byteOffset, bytes.byteLength);
  let at = PNG_SIG.length;
  let header = null;
  let palette = null;
  let trns = null;
  const idatParts = [];
  let sawIdat = false;
  let ended = false;
  while (at < bytes.length) {
    if (ended) throw new Error('bytes after IEND');
    if (at + 12 > bytes.length) throw new Error('cut-short chunk');
    const len = view.getUint32(at);
    if (len > 0x7fffffff || at + 12 + len > bytes.length) throw new Error('chunk overruns file');
    const type = String.fromCharCode(bytes[at + 4], bytes[at + 5], bytes[at + 6], bytes[at + 7]);
    if (crc32(bytes, at + 4, at + 8 + len) !== view.getUint32(at + 8 + len)) throw new Error(`${type} CRC mismatch`);
    const data = bytes.subarray(at + 8, at + 8 + len);
    at += 12 + len;
    if (!READABLE_CHUNKS.includes(type)) throw new Error(`unreadable chunk ${type}`);
    if (header === null && type !== 'IHDR') throw new Error('first chunk is not IHDR');
    if (type === 'IHDR') {
      if (header !== null) throw new Error('two IHDR chunks');
      if (len !== 13) throw new Error('IHDR is not 13 bytes');
      const dv = new DataView(data.buffer, data.byteOffset, 13);
      header = {
        width: dv.getUint32(0),
        height: dv.getUint32(4),
        depth: data[8],
        colourType: data[9],
        compression: data[10],
        filter: data[11],
        interlace: data[12],
      };
      if (header.depth !== 8) throw new Error('bit depth is not 8');
      if (!(header.colourType in CHANNELS)) throw new Error('colour type not accepted');
      if (header.compression !== 0 || header.filter !== 0 || header.interlace !== 0) {
        throw new Error('compression, filter or interlace method is not 0');
      }
    } else if (type === 'PLTE') {
      if (palette !== null) throw new Error('two PLTE chunks');
      if (header.colourType !== 3) throw new Error('PLTE without colour type 3');
      if (sawIdat) throw new Error('PLTE after IDAT');
      if (len === 0 || len % 3 !== 0 || len > 768) throw new Error('PLTE size is wrong');
      palette = data;
    } else if (type === 'tRNS') {
      if (trns !== null) throw new Error('two tRNS chunks');
      if (sawIdat) throw new Error('tRNS after IDAT');
      const ct = header.colourType;
      if (ct === 3) {
        if (palette === null) throw new Error('tRNS before PLTE');
        if (len > palette.length / 3) throw new Error('tRNS longer than palette');
      } else if (ct === 0 || ct === 2) {
        if (len !== (ct === 0 ? 2 : 6)) throw new Error('tRNS size is wrong for colour type');
        for (let i = 0; i < len; i += 2) if (data[i] !== 0) throw new Error('tRNS sample over 255');
      } else throw new Error(`tRNS with colour type ${ct}`);
      trns = data;
    } else if (type === 'IDAT') {
      sawIdat = true;
      if (header.colourType === 3 && palette === null) throw new Error('IDAT before PLTE');
      idatParts.push(data);
    } else {
      if (len !== 0) throw new Error('IEND is not empty');
      ended = true;
    }
  }
  if (!ended) throw new Error('no IEND');
  if (idatParts.length === 0) throw new Error('no IDAT');
  const { width, height, colourType } = header;
  const bpp = CHANNELS[colourType];
  const stride = width * bpp;
  const expected = height * (stride + 1);
  const raw = inflateSync(idatParts.length === 1 ? idatParts[0] : Buffer.concat(idatParts), {
    maxOutputLength: expected + 1,
  });
  if (raw.length !== expected) throw new Error(`IDAT inflates to ${raw.length} bytes, not ${expected}`);

  const samples = new Uint8Array(height * stride);
  for (let y = 0; y < height; y++) {
    const ft = raw[y * (stride + 1)];
    if (ft > 4) throw new Error(`row ${y} filter ${ft}`);
    const src = y * (stride + 1) + 1;
    const o = y * stride;
    const p = o - stride;
    if (ft === 0) {
      samples.set(raw.subarray(src, src + stride), o);
    } else if (ft === 1) {
      for (let i = 0; i < stride; i++) samples[o + i] = raw[src + i] + (i >= bpp ? samples[o + i - bpp] : 0);
    } else if (ft === 2) {
      for (let i = 0; i < stride; i++) samples[o + i] = raw[src + i] + (y > 0 ? samples[p + i] : 0);
    } else if (ft === 3) {
      for (let i = 0; i < stride; i++) {
        samples[o + i] = raw[src + i] + (((i >= bpp ? samples[o + i - bpp] : 0) + (y > 0 ? samples[p + i] : 0)) >> 1);
      }
    } else {
      for (let i = 0; i < stride; i++) {
        const a = i >= bpp ? samples[o + i - bpp] : 0;
        const b = y > 0 ? samples[p + i] : 0;
        const c = y > 0 && i >= bpp ? samples[p + i - bpp] : 0;
        samples[o + i] = raw[src + i] + paethPredictor(a, b, c);
      }
    }
  }

  const n = width * height;
  const rgba = new Uint8Array(n * 4);
  if (colourType === 6) {
    rgba.set(samples);
  } else if (colourType === 2) {
    const key = trns === null ? -1 : (trns[1] << 16) | (trns[3] << 8) | trns[5];
    for (let i = 0, s = 0, d = 0; i < n; i++, s += 3, d += 4) {
      rgba[d] = samples[s];
      rgba[d + 1] = samples[s + 1];
      rgba[d + 2] = samples[s + 2];
      rgba[d + 3] = ((samples[s] << 16) | (samples[s + 1] << 8) | samples[s + 2]) === key ? 0 : 255;
    }
  } else if (colourType === 0) {
    const key = trns === null ? -1 : trns[1];
    for (let i = 0, d = 0; i < n; i++, d += 4) {
      const g = samples[i];
      rgba[d] = rgba[d + 1] = rgba[d + 2] = g;
      rgba[d + 3] = g === key ? 0 : 255;
    }
  } else if (colourType === 4) {
    for (let i = 0, s = 0, d = 0; i < n; i++, s += 2, d += 4) {
      rgba[d] = rgba[d + 1] = rgba[d + 2] = samples[s];
      rgba[d + 3] = samples[s + 1];
    }
  } else {
    const entries = palette.length / 3;
    const lut = new Uint8Array(entries * 4);
    for (let e = 0; e < entries; e++) {
      lut[e * 4] = palette[e * 3];
      lut[e * 4 + 1] = palette[e * 3 + 1];
      lut[e * 4 + 2] = palette[e * 3 + 2];
      lut[e * 4 + 3] = trns !== null && e < trns.length ? trns[e] : 255;
    }
    for (let i = 0, d = 0; i < n; i++, d += 4) {
      const e = samples[i];
      if (e >= entries) throw new Error(`pixel ${i} names palette entry ${e} of ${entries}`);
      rgba[d] = lut[e * 4];
      rgba[d + 1] = lut[e * 4 + 1];
      rgba[d + 2] = lut[e * 4 + 2];
      rgba[d + 3] = lut[e * 4 + 3];
    }
  }
  return { width, height, rgba };
}

// ---------------------------------------------------------------------------
// PNG row filters and their per-row costs.
// ---------------------------------------------------------------------------

/** Filter one row of `cur` (stride samples, `prev` the row above or null) by `type` into `out`. */
function filterRow(type, cur, prev, bpp, out) {
  const n = cur.length;
  if (type === 0) {
    out.set(cur);
  } else if (type === 1) {
    for (let i = 0; i < n; i++) out[i] = cur[i] - (i >= bpp ? cur[i - bpp] : 0);
  } else if (type === 2) {
    for (let i = 0; i < n; i++) out[i] = cur[i] - (prev === null ? 0 : prev[i]);
  } else if (type === 3) {
    for (let i = 0; i < n; i++) {
      out[i] = cur[i] - (((i >= bpp ? cur[i - bpp] : 0) + (prev === null ? 0 : prev[i])) >> 1);
    }
  } else {
    for (let i = 0; i < n; i++) {
      const a = i >= bpp ? cur[i - bpp] : 0;
      const b = prev === null ? 0 : prev[i];
      const c = prev !== null && i >= bpp ? prev[i - bpp] : 0;
      out[i] = cur[i] - paethPredictor(a, b, c);
    }
  }
}

/** Sum of a filtered row's bytes read as signed values, absolute. Lower predicts smaller. */
function signedSum(row) {
  let s = 0;
  for (let i = 0; i < row.length; i++) {
    const v = row[i];
    s += v < 128 ? v : 256 - v;
  }
  return s;
}

/** How many distinct neighbouring byte pairs a filtered row holds. Lower predicts smaller. */
function distinctPairs(row, seen, stamp) {
  let n = 0;
  for (let i = 1; i < row.length; i++) {
    const pair = (row[i - 1] << 8) | row[i];
    if (seen[pair] !== stamp) {
      seen[pair] = stamp;
      n++;
    }
  }
  return n;
}

// ---------------------------------------------------------------------------
// What the image holds: opacity, greyness, and its colours when few.
// ---------------------------------------------------------------------------

/** Scan RGBA pixels: whether all are opaque, all grey, and the colour counts when at most 256. */
function analyse(rgba) {
  const n = rgba.length >>> 2;
  let opaque = true;
  let grey = true;
  const counts = new Map();
  let many = false;
  for (let i = 0, d = 0; i < n; i++, d += 4) {
    if (rgba[d + 3] !== 255) opaque = false;
    if (rgba[d] !== rgba[d + 1] || rgba[d] !== rgba[d + 2]) grey = false;
    if (!many) {
      const word = (rgba[d] | (rgba[d + 1] << 8) | (rgba[d + 2] << 16) | (rgba[d + 3] << 24)) >>> 0;
      const k = counts.get(word);
      if (k === undefined) {
        if (counts.size === 256) many = true;
        else counts.set(word, 1);
      } else counts.set(word, k + 1);
    }
  }
  let colours = null;
  if (!many) {
    colours = [...counts.entries()].map(([word, count]) => ({
      r: word & 0xff,
      g: (word >>> 8) & 0xff,
      b: (word >>> 16) & 0xff,
      a: (word >>> 24) & 0xff,
      word,
      count,
    }));
  }
  return { opaque, grey, colours };
}

/**
 * The one fully-transparent value (a grey sample, or an RGB triple) the image
 * may key by tRNS instead of carrying an alpha channel: every non-opaque pixel
 * is that exact value at alpha 0, and no opaque pixel shares the value.
 * Null when there is none.
 */
function transparentKey(rgba, grey) {
  let key = -1;
  for (let d = 0; d < rgba.length; d += 4) {
    const a = rgba[d + 3];
    if (a === 255) continue;
    if (a !== 0) return null;
    const v = grey ? rgba[d] : (rgba[d] << 16) | (rgba[d + 1] << 8) | rgba[d + 2];
    if (key === -1) key = v;
    else if (key !== v) return null;
  }
  if (key === -1) return null;
  for (let d = 0; d < rgba.length; d += 4) {
    if (rgba[d + 3] !== 255) continue;
    const v = grey ? rgba[d] : (rgba[d] << 16) | (rgba[d + 1] << 8) | rgba[d + 2];
    if (v === key) return null;
  }
  return key;
}

/** The image's samples in colour type `ct` (0, 2, 4 or 6) from its RGBA. */
function samplesOf(rgba, ct) {
  const n = rgba.length >>> 2;
  if (ct === 6) return rgba;
  const ch = ct === 0 ? 1 : ct === 4 ? 2 : 3;
  const out = new Uint8Array(n * ch);
  for (let i = 0, d = 0, s = 0; i < n; i++, d += 4, s += ch) {
    if (ct === 0) out[s] = rgba[d];
    else if (ct === 4) {
      out[s] = rgba[d];
      out[s + 1] = rgba[d + 3];
    } else {
      out[s] = rgba[d];
      out[s + 1] = rgba[d + 1];
      out[s + 2] = rgba[d + 2];
    }
  }
  return out;
}

// ---------------------------------------------------------------------------
// Palette forms.
// ---------------------------------------------------------------------------

function luminance(c) {
  return 299 * c.r + 587 * c.g + 114 * c.b;
}

/** Palette entries in write order: transparent ones first (by alpha), then by `order`. */
function paletteEntries(colours, order) {
  return [...colours].sort((x, y) => {
    const tx = x.a === 255 ? 1 : 0;
    const ty = y.a === 255 ? 1 : 0;
    if (tx !== ty) return tx - ty;
    if (tx === 0 && x.a !== y.a) return x.a - y.a;
    if (order === 'luminance') return luminance(x) - luminance(y) || x.word - y.word;
    return y.count - x.count || x.word - y.word;
  });
}

/** The palette form of an image: PLTE, tRNS (when any entry is transparent) and per-pixel indices. */
function paletteForm(rgba, colours, order) {
  const entries = paletteEntries(colours, order);
  const index = new Map(entries.map((c, i) => [c.word, i]));
  const plte = new Uint8Array(entries.length * 3);
  let transparent = 0;
  entries.forEach((c, i) => {
    plte[i * 3] = c.r;
    plte[i * 3 + 1] = c.g;
    plte[i * 3 + 2] = c.b;
    if (c.a !== 255) transparent = i + 1;
  });
  const trns = transparent === 0 ? null : Uint8Array.from(entries.slice(0, transparent), (c) => c.a);
  const n = rgba.length >>> 2;
  const indices = new Uint8Array(n);
  for (let i = 0, d = 0; i < n; i++, d += 4) {
    const word = (rgba[d] | (rgba[d + 1] << 8) | (rgba[d + 2] << 16) | (rgba[d + 3] << 24)) >>> 0;
    indices[i] = index.get(word);
  }
  return { plte, trns, indices };
}

// ---------------------------------------------------------------------------
// Filtering a whole image by a choice of per-row filters.
// ---------------------------------------------------------------------------

const BRUTE_CONTEXT = 32768;
const BRUTE_LEVEL = 4;

/**
 * The raw filtered data of `samples` (height rows of width x bpp), each row
 * behind its filter byte. `choice` is one fixed filter (0..4) for every row,
 * or 'minsum', 'pairs' or 'brute': per row, the filter with the least signed
 * sum, the fewest distinct byte pairs, or the smallest real level-4 deflate
 * of the row against the 32 KiB written before it. The lower filter wins a tie.
 */
function filteredData(samples, width, height, bpp, choice) {
  const stride = width * bpp;
  const raw = new Uint8Array(height * (stride + 1));
  const trial = Array.from({ length: 5 }, () => new Uint8Array(stride + 1));
  for (let t = 0; t < 5; t++) trial[t][0] = t;
  const seen = new Uint32Array(65536);
  let stamp = 0;
  for (let y = 0; y < height; y++) {
    const cur = samples.subarray(y * stride, (y + 1) * stride);
    const prev = y === 0 ? null : samples.subarray((y - 1) * stride, y * stride);
    const at = y * (stride + 1);
    if (typeof choice === 'number') {
      raw[at] = choice;
      filterRow(choice, cur, prev, bpp, raw.subarray(at + 1, at + 1 + stride));
      continue;
    }
    const before = raw.subarray(Math.max(0, at - BRUTE_CONTEXT), at);
    let type = 0;
    let best = Infinity;
    for (let t = 0; t < 5; t++) {
      filterRow(t, cur, prev, bpp, trial[t].subarray(1));
      let cost;
      if (choice === 'minsum') cost = signedSum(trial[t].subarray(1));
      else if (choice === 'pairs') cost = distinctPairs(trial[t].subarray(1), seen, ++stamp);
      else {
        cost = deflateSync(trial[t], before.length === 0
          ? { level: BRUTE_LEVEL, memLevel: 9 }
          : { level: BRUTE_LEVEL, memLevel: 9, dictionary: before }).length;
      }
      if (cost < best) {
        best = cost;
        type = t;
      }
    }
    raw.set(trial[type], at);
  }
  return raw;
}

/** The filter choices each form is screened with. */
const PALETTE_FILTERS = [0, 'minsum', 'brute'];
const CHANNEL_FILTERS = [0, 1, 2, 4, 'minsum', 'pairs', 'brute'];

/**
 * The forms an image can be written in, each {colourType, bpp, samples, plte,
 * trns, filters}: palette forms when it holds at most 256 colours (a palette
 * of a non-grey image is never beaten by its RGB form), else a grey or
 * RGB(A) form, with a tRNS key when one transparent value covers every
 * non-opaque pixel.
 */
function formsOf(rgba) {
  const { opaque, grey, colours } = analyse(rgba);
  const forms = [];
  if (colours !== null) {
    for (const order of ['count', 'luminance']) {
      const p = paletteForm(rgba, colours, order);
      forms.push({ colourType: 3, bpp: 1, samples: p.indices, plte: p.plte, trns: p.trns, filters: PALETTE_FILTERS });
    }
    if (!grey) return forms;
  }
  const key = opaque ? null : transparentKey(rgba, grey);
  let ct;
  let trns = null;
  if (grey) {
    ct = opaque || key !== null ? 0 : 4;
    if (key !== null) trns = Uint8Array.of(0, key);
  } else {
    ct = opaque || key !== null ? 2 : 6;
    if (key !== null) trns = Uint8Array.of(0, key >>> 16, 0, (key >>> 8) & 0xff, 0, key & 0xff);
  }
  const bpp = { 0: 1, 2: 3, 4: 2, 6: 4 }[ct];
  forms.push({ colourType: ct, bpp, samples: samplesOf(rgba, ct), plte: null, trns, filters: CHANNEL_FILTERS });
  return forms;
}

// ---------------------------------------------------------------------------
// Screening the forms, then the final squeeze.
// ---------------------------------------------------------------------------

/** The bytes a form's PLTE and tRNS chunks add to its file. */
function extraChunks(form) {
  return (form.plte === null ? 0 : 12 + form.plte.length) + (form.trns === null ? 0 : 12 + form.trns.length);
}

/** True when `stream` inflates back to exactly `raw` (a zlib stream, header and Adler included). */
function roundTrips(stream, raw) {
  try {
    const back = inflateSync(stream, { maxOutputLength: raw.length + 1 });
    return back.length === raw.length && back.every((b, i) => b === raw[i]);
  } catch {
    return false;
  }
}

/**
 * zlib level 9 of `raw` with the stream split into fresh-Huffman blocks
 * every `rowsPerBlock` rows: each block boundary is a Z_BLOCK flush, so the
 * block gets Huffman tables fitted to its own rows while the LZ77 window
 * carries over. The split points are fixed row counts, so the bytes are
 * deterministic. Returns null on any error.
 */
function z9split(raw, rowLen, rowsPerBlock) {
  return new Promise((resolve) => {
    const d = createDeflate({ level: 9, memLevel: 9 });
    const chunks = [];
    d.on('data', (c) => chunks.push(c));
    d.on('error', () => resolve(null));
    d.on('end', () => resolve(Buffer.concat(chunks)));
    const rows = Math.floor(raw.length / rowLen);
    let i = 0;
    const step = () => {
      if (i >= rows) { d.end(); return; }
      const n = Math.min(rowsPerBlock, rows - i);
      const end = i + n;
      const more = end < rows;
      d.write(raw.subarray(i * rowLen, end * rowLen), () => {
        i = end;
        if (more) d.flush(constants.Z_BLOCK, step);
        else step();
      });
    };
    step();
  });
}

/**
 * The smallest zlib stream of `raw`: level 9 (default and filtered
 * strategies), level 9 with block splits at row boundaries, and the
 * optimal-parse encoder. The optimal encoder runs on every stream now:
 * it beats level 9 on the practice set at every size, and its block
 * splitting adapts the Huffman tables to the image's regions. Every
 * candidate that is not zlib's own output is inflated back and only
 * trusted when it reproduces `raw` exactly. Deterministic throughout:
 * fixed split points, fixed iteration counts, no clock.
 */
async function compressBest(raw, rowLen) {
  let best = deflateSync(raw, { level: 9, memLevel: 9 });
  const filtered = deflateSync(raw, { level: 9, memLevel: 9, strategy: constants.Z_FILTERED });
  if (filtered.length < best.length) best = filtered;
  for (const rowsPerBlock of [64, 128]) {
    const split = await z9split(raw, rowLen, rowsPerBlock);
    if (split !== null && split.length < best.length && roundTrips(split, raw)) best = split;
  }
  const optimal = optimalDeflate2(raw, rowLen);
  if (optimal !== null && optimal.length < best.length && roundTrips(optimal, raw)) best = optimal;
  return new Uint8Array(best.buffer, best.byteOffset, best.length);
}

/** The squeezed PNG of one RGBA image: the best form and filter choice, deflated best. */
async function squeeze(rgba, width, height) {
  let best = null;
  for (const form of formsOf(rgba)) {
    const chunks = extraChunks(form);
    for (const choice of form.filters) {
      const data = filteredData(form.samples, width, height, form.bpp, choice);
      const zlib = deflateSync(data, { level: 6, memLevel: 8 });
      const bytes = zlib.length + chunks;
      if (best === null || bytes < best.bytes) best = { form, data, bytes };
    }
  }
  const rowLen = width * best.form.bpp + 1;
  const idat = await compressBest(best.data, rowLen);
  const chunks = [['IHDR', ihdrData(width, height, best.form.colourType)]];
  if (best.form.plte !== null) chunks.push(['PLTE', best.form.plte]);
  if (best.form.trns !== null) chunks.push(['tRNS', best.form.trns]);
  chunks.push(['IDAT', idat]);
  chunks.push(['IEND', new Uint8Array(0)]);
  return pngFile(chunks);
}

for (const id of readdirSync(IN_DIR).sort()) {
  const image = decodePng(new Uint8Array(readFileSync(join(IN_DIR, id, 'image.png'))));
  if (image.width !== 1280 || image.height !== 720) throw new Error(`${id} is ${image.width}x${image.height}, not 1280x720`);
  mkdirSync(join(OUT_DIR, id), { recursive: true });
  writeFileSync(join(OUT_DIR, id, 'image.png'), await squeeze(image.rgba, image.width, image.height));
}
