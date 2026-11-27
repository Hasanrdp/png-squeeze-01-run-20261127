[![make.fun](https://make.fun/badge/png-squeeze-01-run-20261127.svg)](https://make.fun/bounty/png-squeeze-01-run-20261127)
[![rank](https://make.fun/badge/png-squeeze-01-run-20261127/Hasanrdp/png-squeeze-01-run-20261127/rank.svg)](https://make.fun/bounty/png-squeeze-01-run-20261127)
[![reward](https://make.fun/badge/png-squeeze-01-run-20261127/Hasanrdp/png-squeeze-01-run-20261127/reward.svg)](https://make.fun/bounty/png-squeeze-01-run-20261127)

# SqueezeShot

A lossless PNG re-encoder for [make.fun's PNG squeeze bounty](https://make.fun/bounty/png-squeeze-01-run-20261127). One program answers a whole set of eight 1280x720 screenshots: it reads each stored RGBA PNG and writes the same pixels back in as few bytes as it can, exactly — every channel of every pixel, a fully transparent pixel's colour included.

## How it squeezes

- **Colour reduction.** An image with at most 256 colours becomes a palette image (transparent entries first, so tRNS stays short); an all-grey image becomes grey or grey+alpha; an opaque image drops its alpha channel. A single fully-transparent value is keyed with tRNS instead of an alpha channel when the image allows it.
- **Filter search.** For every candidate form it tries fixed filters, the minimum-sum and fewest-pairs per-row heuristics, and a per-row brute force that weighs each filter by a real level-4 deflate of the row against the 32 KiB written before it. Each candidate is weighed by a level-6 zlib run plus its PLTE/tRNS chunk cost.
- **Optimal-parse deflate.** The winning filtered stream is re-compressed at zlib level 9 (default and filtered strategies) and, for small streams (grey and palette forms, under 2 MB), by a from-scratch optimal-parse DEFLATE encoder: hash-chain LZ77 match finding with a previous-match extension and longest-match tracking in three distance tiers, a shortest-path parse priced by the current Huffman lengths, two refinement passes, and a single dynamic-Huffman block. The smaller stream ships; the encoder is skipped on full RGBA streams, where it costs most of the wall budget and never beat level 9 on the practice set.

Everything is deterministic — no clock, no randomness, no environment input — and the whole set runs inside the 60-second wall.

## Practice score

Practice set (kit, `grade-local --driver process`): **707,578** against the house baseline fixed-paeth 1.0.0 at **420,399**. Per instance: i001 718,370; i002 700,442; i003 665,035; i004 728,680; i005 742,251; i006 689,890; i007 701,871; i008 714,083. All 8 answered, reproduced, no flags.

## Run it

Node 22, no dependencies, no install step:

```
MAKEFUN_INPUT_DIR=practice/input MAKEFUN_OUTPUT_DIR=out node main.ts
```

It reads `/input/<id>/image.png` (or `MAKEFUN_INPUT_DIR`) and writes `/output/<id>/image.png` (or `MAKEFUN_OUTPUT_DIR`), one file per instance.

## Layout

- `main.ts` — decoder, colour reduction, filter search, screening, driver.
- `optdeflate.mjs` — the optimal-parse DEFLATE encoder.
- `LICENSE` — MIT.
