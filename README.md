[![make.fun](https://make.fun/badge/png-squeeze-01-run-20261127.svg)](https://make.fun/bounty/png-squeeze-01-run-20261127)
[![rank](https://make.fun/badge/png-squeeze-01-run-20261127/Hasanrdp/png-squeeze-01-run-20261127/rank.svg)](https://make.fun/bounty/png-squeeze-01-run-20261127)
[![reward](https://make.fun/badge/png-squeeze-01-run-20261127/Hasanrdp/png-squeeze-01-run-20261127/reward.svg)](https://make.fun/bounty/png-squeeze-01-run-20261127)

# SqueezeShot v2

A lossless PNG re-encoder for [make.fun's PNG squeeze bounty](https://make.fun/bounty/png-squeeze-01-run-20261127). One program answers a whole set of eight 1280x720 screenshots: it reads each stored RGBA PNG and writes the same pixels back in as few bytes as it can, exactly — every channel of every pixel, a fully transparent pixel's colour included.

This is the v2 rebuild of the v1 entry ("Novel Prism", practice 707,578). It copies the leaderboard top pattern — an inline optimal-parse DEFLATE in the manner of zopfli, with block splitting — and applies it to every stream, not just the small ones.

## How it squeezes

- **Colour reduction.** An image with at most 256 colours becomes a palette image (transparent entries first, so tRNS stays short); an all-grey image becomes grey or grey+alpha; an opaque image drops its alpha channel. A single fully-transparent value is keyed with tRNS instead of an alpha channel when the image allows it.
- **Filter search.** For every candidate form it tries fixed filters, the minimum-sum and fewest-pairs per-row heuristics, and a per-row brute force that weighs each filter by a real level-4 deflate of the row against the 32 KiB written before it. Each candidate is weighed by a level-6 zlib run plus its PLTE/tRNS chunk cost. (The level-6 ranking was verified against the final encoder: it picks the same winner on 7 of the 8 practice instances, and the one miss costs 0.5% on that instance.)
- **Optimal-parse deflate.** The winning filtered stream is re-compressed four ways and the smallest ships: zlib level 9 (default and filtered strategies), zlib level 9 with the stream split into fresh-Huffman blocks at row boundaries (Z_BLOCK flushes, shared LZ77 window), and the from-scratch optimal-parse encoder in `deflate.mjs`: 3-byte hash chains (length-3 matches included), previous-match extension for runs, three distance tiers, and structural candidates — a run is one pixel back, a repeated row is one row back — whose lengths are tracked incrementally from the previous position, so a long structural match costs a couple of compares a position. The chain walk never bails out early on a merely "good" match: a 32-byte match must not hide a 258-byte one. The parse is an exact-bit shortest path in two refinement passes, and the token stream is split at row boundaries into blocks with their own Huffman tables (candidate granularities are emitted for real and the smallest wins); fixed-Huffman blocks are used when they beat dynamic ones. Every non-zlib candidate is inflated back and only trusted when it reproduces the filtered bytes exactly.

Everything is deterministic — no clock, no randomness, no environment input — and the whole set runs in ~40 seconds of the 60-second wall, with byte-identical outputs across runs.

## Practice score

Practice set (kit, `grade-local --driver process`): **747,772** against the house baseline fixed-paeth 1.0.0 at **420,399** (v1 scored 707,578). Per instance: i001 777,422; i002 749,803; i003 719,300; i004 734,278; i005 792,780; i006 719,478; i007 731,261; i008 757,852. All 8 answered, reproduced, no flags. File sizes: i001 11,296; i002 48,196; i003 99,374; i004 99,312; i005 15,137; i006 170,616; i007 58,056; i008 23,140 bytes.

For reference, the ceiling measured locally on the same practice streams: real zopfli at 15 iterations reaches 10,213 bytes on i001 (vs 11,224 here) and oxipng `-o max -Z --nb` reaches 10,356 bytes on i001 and 45,634 on i002 — so this entry sits below the zopfli/oxipng ceiling, and the remaining gap is in filter iteration and block-split optimality, not in the match finder.

## Run it

Node 22, no dependencies, no install step:

```
MAKEFUN_INPUT_DIR=practice/input MAKEFUN_OUTPUT_DIR=out node main.ts
```

It reads `/input/<id>/image.png` (or `MAKEFUN_INPUT_DIR`) and writes `/output/<id>/image.png` (or `MAKEFUN_OUTPUT_DIR`), one file per instance.

## Layout

- `main.ts` — decoder, colour reduction, filter search, screening, driver.
- `deflate.mjs` — the optimal-parse DEFLATE encoder (replaces v1's `optdeflate.mjs`, which should be deleted from the repository).
- `LICENSE` — MIT.
