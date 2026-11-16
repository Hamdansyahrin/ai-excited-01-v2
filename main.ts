// "The Glass Phoenix" — a colossal phoenix of stained glass and living flame
// over a mirror sea at sunset. Procedurally painted, deterministic, stdlib only.
import { mkdirSync, writeFileSync } from "node:fs";
import { join } from "node:path";
import { deflateSync } from "node:zlib";
import { createHash } from "node:crypto";

const W = 1024;
const H = 1024;
const HY = 716; // horizon line: sea occupies the lower ~30%

// ---------- seeded RNG (mulberry32) ----------
function mulberry32(seed: number): () => number {
  let a = seed >>> 0;
  return () => {
    a = (a + 0x6d2b79f5) >>> 0;
    let t = a;
    t = Math.imul(t ^ (t >>> 15), t | 1);
    t ^= t + Math.imul(t ^ (t >>> 7), t | 61);
    return ((t ^ (t >>> 14)) >>> 0) / 4294967296;
  };
}
const rng = mulberry32(0x9e3779b9);

// ---------- deterministic 2D hash / value noise ----------
function hash2(ix: number, iy: number): number {
  let n = (ix * 374761393 + iy * 668265263) | 0;
  n = Math.imul(n ^ (n >>> 13), 1274126177);
  return ((n ^ (n >>> 16)) >>> 0) / 4294967296;
}
function smooth(t: number): number {
  return t * t * (3 - 2 * t);
}
function valueNoise(x: number, y: number): number {
  const ix = Math.floor(x);
  const iy = Math.floor(y);
  const fx = smooth(x - ix);
  const fy = smooth(y - iy);
  const a = hash2(ix, iy);
  const b = hash2(ix + 1, iy);
  const c = hash2(ix, iy + 1);
  const d = hash2(ix + 1, iy + 1);
  return a + (b - a) * fx + (c - a) * fy + (a - b - c + d) * fx * fy;
}
function fbm(x: number, y: number, octaves: number): number {
  let sum = 0;
  let amp = 0.5;
  let freq = 1;
  let norm = 0;
  for (let o = 0; o < octaves; o++) {
    sum += amp * valueNoise(x * freq, y * freq);
    norm += amp;
    amp *= 0.5;
    freq *= 2.03;
  }
  return sum / norm;
}

// ---------- HDR float frame buffer ----------
const buf = new Float32Array(W * H * 3);

function clamp(v: number, lo: number, hi: number): number {
  return v < lo ? lo : v > hi ? hi : v;
}
function lerp(a: number, b: number, t: number): number {
  return a + (b - a) * t;
}
type RGB = [number, number, number];
function mixc(a: RGB, b: RGB, t: number): RGB {
  return [lerp(a[0], b[0], t), lerp(a[1], b[1], t), lerp(a[2], b[2], t)];
}
function setPx(x: number, y: number, c: RGB): void {
  const i = (y * W + x) * 3;
  buf[i] = c[0];
  buf[i + 1] = c[1];
  buf[i + 2] = c[2];
}
function addPx(x: number, y: number, c: RGB, s: number): void {
  const i = (y * W + x) * 3;
  buf[i] += c[0] * s;
  buf[i + 1] += c[1] * s;
  buf[i + 2] += c[2] * s;
}
function blendPx(x: number, y: number, c: RGB, alpha: number): void {
  if (alpha <= 0) return;
  const i = (y * W + x) * 3;
  const ia = 1 - alpha;
  buf[i] = buf[i] * ia + c[0] * alpha;
  buf[i + 1] = buf[i + 1] * ia + c[1] * alpha;
  buf[i + 2] = buf[i + 2] * ia + c[2] * alpha;
}
function sampleBilinear(x: number, y: number): RGB {
  const x0 = clamp(Math.floor(x), 0, W - 2);
  const y0 = clamp(Math.floor(y), 0, H - 2);
  const fx = clamp(x - x0, 0, 1);
  const fy = clamp(y - y0, 0, 1);
  const i00 = (y0 * W + x0) * 3;
  const i10 = i00 + 3;
  const i01 = i00 + W * 3;
  const i11 = i01 + 3;
  const out: RGB = [0, 0, 0];
  for (let k = 0; k < 3; k++) {
    const top = lerp(buf[i00 + k], buf[i10 + k], fx);
    const bot = lerp(buf[i01 + k], buf[i11 + k], fx);
    out[k] = lerp(top, bot, fy);
  }
  return out;
}

// ---------- palette ----------
const INDIGO: RGB = [0.016, 0.024, 0.11];
const VIOLET: RGB = [0.27, 0.09, 0.52];
const CRIMSON: RGB = [1.12, 0.2, 0.1];
const EMBER: RGB = [1.08, 0.4, 0.05];
const GOLD: RGB = [1.0, 0.74, 0.36];
const MAGENTA: RGB = [1.05, 0.16, 0.55];
const WHITE_GOLD: RGB = [1.0, 0.93, 0.78];
const DEEP_RED: RGB = [0.5, 0.05, 0.05];

// ---------- PNG encoder (own, per-row adaptive filtering) ----------
const crcTable = new Int32Array(256);
for (let n = 0; n < 256; n++) {
  let c = n;
  for (let k = 0; k < 8; k++) c = c & 1 ? 0xedb88320 ^ (c >>> 1) : c >>> 1;
  crcTable[n] = c;
}
function crc32(data: Buffer): number {
  let c = 0xffffffff;
  for (let i = 0; i < data.length; i++) {
    c = crcTable[(c ^ data[i]) & 0xff] ^ (c >>> 8);
  }
  return (c ^ 0xffffffff) >>> 0;
}
function pngChunk(type: string, data: Buffer): Buffer {
  const len = Buffer.alloc(4);
  len.writeUInt32BE(data.length, 0);
  const body = Buffer.concat([Buffer.from(type, "ascii"), data]);
  const crc = Buffer.alloc(4);
  crc.writeUInt32BE(crc32(body), 0);
  return Buffer.concat([len, body, crc]);
}
function encodePNG(rgb: Uint8Array): Buffer {
  const ihdr = Buffer.alloc(13);
  ihdr.writeUInt32BE(W, 0);
  ihdr.writeUInt32BE(H, 4);
  ihdr[8] = 8; // bit depth
  ihdr[9] = 2; // colour type RGB
  const stride = W * 3;
  const raw = Buffer.alloc(H * (stride + 1));
  const filtered = new Int8Array(stride);
  const prevRow = new Int32Array(stride);
  const curRow = new Int32Array(stride);
  for (let y = 0; y < H; y++) {
    const rowOff = y * stride;
    for (let i = 0; i < stride; i++) curRow[i] = rgb[rowOff + i];
    let bestFilter = 0;
    let bestScore = Infinity;
    let bestBytes: Int8Array | null = null;
    for (let f = 0; f < 5; f++) {
      let score = 0;
      for (let i = 0; i < stride; i++) {
        const a = i >= 3 ? curRow[i - 3] : 0;
        const b = prevRow[i];
        const c = i >= 3 ? prevRow[i - 3] : 0;
        let pred = 0;
        if (f === 1) pred = a;
        else if (f === 2) pred = b;
        else if (f === 3) pred = (a + b) >> 1;
        else if (f === 4) {
          const p = a + b - c;
          const pa = Math.abs(p - a);
          const pb = Math.abs(p - b);
          const pc = Math.abs(p - c);
          pred = pa <= pb && pa <= pc ? a : pb <= pc ? b : c;
        }
        const v = (curRow[i] - pred) & 0xff;
        filtered[i] = v < 128 ? v : v - 256;
        score += Math.abs(filtered[i]);
        if (score >= bestScore) break;
      }
      if (score < bestScore) {
        bestScore = score;
        bestFilter = f;
        bestBytes = Int8Array.from(filtered);
      }
    }
    const outOff = y * (stride + 1);
    raw[outOff] = bestFilter;
    for (let i = 0; i < stride; i++) raw[outOff + 1 + i] = bestBytes![i] & 0xff;
    for (let i = 0; i < stride; i++) prevRow[i] = curRow[i];
  }
  const idat = deflateSync(raw, { level: 9 });
  return Buffer.concat([
    Buffer.from([137, 80, 78, 71, 13, 10, 26, 10]),
    pngChunk("IHDR", ihdr),
    pngChunk("IDAT", idat),
    pngChunk("IEND", Buffer.alloc(0)),
  ]);
}

// ---------- sky: sunset gradient + low-res fBm cloud field, upscaled ----------
function renderSky(): void {
  // cloud field at 256x256, 4-octave fBm
  const CS = 256;
  const cloud = new Float32Array(CS * CS);
  for (let y = 0; y < CS; y++) {
    for (let x = 0; x < CS; x++) {
      const warp = fbm(x * 0.012 + 40, y * 0.012 + 9, 3);
      cloud[y * CS + x] = fbm(x * 0.02 + warp * 2.2, y * 0.045, 4);
    }
  }
  const cloudAt = (x: number, y: number): number => {
    const gx = clamp((x / W) * (CS - 1), 0, CS - 2);
    const gy = clamp((y / H) * (CS - 1), 0, CS - 2);
    const x0 = Math.floor(gx);
    const y0 = Math.floor(gy);
    const fx = gx - x0;
    const fy = gy - y0;
    const i = y0 * CS + x0;
    return lerp(
      lerp(cloud[i], cloud[i + 1], fx),
      lerp(cloud[i + CS], cloud[i + CS + 1], fx),
      fy,
    );
  };

  for (let y = 0; y < H; y++) {
    const v = y / H; // 0 top .. 1 bottom
    // sunset gradient stops
    let base: RGB;
    if (v < 0.34) base = mixc(INDIGO, VIOLET, smooth(v / 0.34));
    else if (v < 0.55) base = mixc(VIOLET, CRIMSON, smooth((v - 0.34) / 0.21));
    else if (v < 0.68) base = mixc(CRIMSON, EMBER, smooth((v - 0.55) / 0.13));
    else base = mixc(EMBER, GOLD, smooth(clamp((v - 0.68) / 0.1, 0, 1)));
    for (let x = 0; x < W; x++) {
      const cl = cloudAt(x, y);
      // cloud banks: stronger mid-sky, stretched horizontally
      const band = Math.sin(Math.PI * clamp((v - 0.06) / 0.62, 0, 1));
      const density = clamp((cl - 0.46) * 2.6, 0, 1) * band;
      // cloud colour: lit gold near horizon/sun side, violet shadow up top
      const lit = clamp(1.15 - v * 1.15, 0, 1);
      const cloudCol = mixc(
        mixc(VIOLET, CRIMSON, lit),
        GOLD,
        clamp(lit * lit * 0.85, 0, 1),
      );
      const shade = 0.55 + 0.45 * cl;
      let col = mixc(base, cloudCol, density * 0.8);
      col = [col[0] * shade + density * 0.08, col[1] * shade, col[2] * shade];
      // darken the very top for HDR headroom
      const topDim = 0.55 + 0.45 * smooth(clamp(v / 0.25, 0, 1));
      setPx(x, y, [col[0] * topDim, col[1] * topDim, col[2] * topDim]);
    }
  }
}

// ---------- sun disc, halo and god rays ----------
const SUN_X = 512;
const SUN_Y = 700;
const SUN_R = 126;
function renderSun(): void {
  // wide halo (additive)
  for (let y = 0; y < HY + 30; y++) {
    for (let x = 0; x < W; x++) {
      const dx = x - SUN_X;
      const dy = y - SUN_Y;
      const d = Math.sqrt(dx * dx + dy * dy);
      const halo = Math.exp(-d / 340) * 0.78 + Math.exp(-d / 110) * 0.85;
      addPx(x, y, GOLD, halo);
      // god-ray shafts fanning upward from the sun
      if (dy < -20) {
        const ang = Math.atan2(-dy, dx); // 0..PI above sun
        let ray = 0;
        const shafts: Array<[number, number, number]> = [
          [0.45, 0.055, 0.5],
          [0.85, 0.04, 0.75],
          [1.25, 0.07, 0.6],
          [1.62, 0.045, 0.9],
          [2.0, 0.06, 0.65],
          [2.45, 0.04, 0.8],
          [2.85, 0.065, 0.5],
        ];
        for (const [sa, sw, ss] of shafts) {
          const da = ang - sa;
          ray += ss * Math.exp(-(da * da) / (2 * sw * sw));
        }
        const fall = Math.exp(-d / 780) * clamp((-dy - 20) / 120, 0, 1);
        addPx(x, y, GOLD, ray * fall * 0.62);
      }
    }
  }
  // disc with soft limb
  const r0 = SUN_R - 6;
  for (let y = SUN_Y - SUN_R - 4; y <= SUN_Y + SUN_R + 4; y++) {
    if (y < 0 || y >= H) continue;
    for (let x = SUN_X - SUN_R - 4; x <= SUN_X + SUN_R + 4; x++) {
      if (x < 0 || x >= W) continue;
      const dx = x - SUN_X;
      const dy = y - SUN_Y;
      const d = Math.sqrt(dx * dx + dy * dy);
      const a = clamp((SUN_R - d) / 6 + 0.5, 0, 1);
      if (a <= 0) continue;
      const core = mixc(GOLD, WHITE_GOLD, clamp(1 - d / r0, 0, 1));
      blendPx(x, y, [core[0] * 1.75, core[1] * 1.62, core[2] * 1.4], a);
    }
  }
}

// ---------- feather rasteriser ----------
// A feather is a tapered, slightly bent shape from base (cx,cy) along `angle`.
// Colour comes from colFn(u, edge) where u = 0 base .. 1 tip, edge = |v|/halfW.
interface FeatherOpts {
  bend?: number; // perpendicular bow of the centreline, in px
  glow?: number; // additive inner-glow strength
}
function drawFeather(
  cx: number,
  cy: number,
  angle: number,
  len: number,
  wid: number,
  colFn: (u: number, edge: number) => RGB,
  opts: FeatherOpts = {},
): void {
  const bend = opts.bend ?? 0;
  const glow = opts.glow ?? 0;
  const ex = Math.cos(angle);
  const ey = Math.sin(angle);
  const px = -ey;
  const py = ex;
  const reach = wid * 0.75 + Math.abs(bend) + 3;
  const minX = clamp(Math.floor(Math.min(cx, cx + ex * len) - reach), 0, W - 1);
  const maxX = clamp(Math.ceil(Math.max(cx, cx + ex * len) + reach), 0, W - 1);
  const minY = clamp(Math.floor(Math.min(cy, cy + ey * len) - reach), 0, H - 1);
  const maxY = clamp(Math.ceil(Math.max(cy, cy + ey * len) + reach), 0, H - 1);
  for (let y = minY; y <= maxY; y++) {
    for (let x = minX; x <= maxX; x++) {
      const dx = x - cx;
      const dy = y - cy;
      const along = dx * ex + dy * ey;
      if (along < -2 || along > len + 2) continue;
      const u = clamp(along / len, 0, 1);
      // centreline bows sideways as sin(pi*u)
      const centreOff = bend * Math.sin(Math.PI * u);
      const perp = dx * px + dy * py - centreOff;
      // width profile: narrow base, broad at 55%, pointed tip
      const prof = Math.sin(Math.PI * Math.pow(u, 0.72));
      const halfW = Math.max(0.6, wid * 0.5 * Math.pow(prof, 0.8) * (1 - 0.12 * u));
      const edge = Math.abs(perp) / halfW;
      const alpha = clamp((halfW - Math.abs(perp)) / 1.6 + 0.5, 0, 1);
      if (alpha <= 0) continue;
      const col = colFn(u, edge);
      // bright gold rim on the upper edge (perp < 0 side)
      let r = col[0];
      let g = col[1];
      let b = col[2];
      if (perp < 0 && edge > 0.62) {
        const rim = (edge - 0.62) / 0.38;
        r = lerp(r, 1.35, rim * 0.75);
        g = lerp(g, 1.05, rim * 0.75);
        b = lerp(b, 0.5, rim * 0.6);
      }
      // darker leading (lower) edge for the glass read
      if (perp > 0 && edge > 0.7) {
        const dk = 1 - (edge - 0.7) * 0.9;
        r *= dk;
        g *= dk;
        b *= dk;
      }
      // central shaft highlight
      if (edge < 0.16) {
        const sh = (0.16 - edge) / 0.16;
        r += sh * 0.35;
        g += sh * 0.26;
        b += sh * 0.1;
      }
      blendPx(x, y, [r, g, b], alpha);
      if (glow > 0 && edge < 0.85) {
        addPx(x, y, [r, g * 0.8, b * 0.5], glow * (1 - edge) * alpha * 0.4);
      }
    }
  }
}

// feather colour ramps
function rampHot(u: number): RGB {
  // deep red base -> ember -> gold -> white-gold tip
  if (u < 0.4) return mixc(DEEP_RED, EMBER, u / 0.4);
  if (u < 0.75) return mixc(EMBER, GOLD, (u - 0.4) / 0.35);
  return mixc(GOLD, WHITE_GOLD, (u - 0.75) / 0.25);
}
function rampMagenta(u: number): RGB {
  if (u < 0.45) return mixc([0.45, 0.08, 0.3], MAGENTA, u / 0.45);
  if (u < 0.8) return mixc(MAGENTA, EMBER, (u - 0.45) / 0.35);
  return mixc(EMBER, GOLD, (u - 0.8) / 0.2);
}

// quadratic bezier helper
function bez(
  p0: [number, number],
  p1: [number, number],
  p2: [number, number],
  t: number,
): [number, number] {
  const s = 1 - t;
  return [
    s * s * p0[0] + 2 * s * t * p1[0] + t * t * p2[0],
    s * s * p0[1] + 2 * s * t * p1[1] + t * t * p2[1],
  ];
}
function bezTangent(
  p0: [number, number],
  p1: [number, number],
  p2: [number, number],
  t: number,
): number {
  const dx = 2 * (1 - t) * (p1[0] - p0[0]) + 2 * t * (p2[0] - p1[0]);
  const dy = 2 * (1 - t) * (p1[1] - p0[1]) + 2 * t * (p2[1] - p1[1]);
  return Math.atan2(dy, dx);
}

// ---------- one wing: rows of feathers hanging off a leading-edge arc ----------
function drawWing(
  shoulder: [number, number],
  ctrl: [number, number],
  tip: [number, number],
  rot: number, // feather direction = tangent rotated by this
  mirrorPalette: boolean,
): void {
  const ramp = mirrorPalette ? rampMagenta : rampHot;
  // primaries: long feathers, bases along the leading edge. Denser and wider
  // than pass 1 so they overlap into a surface (no sky gaps), with per-feather
  // angle/length jitter and a dark under-shadow pass for inter-feather depth.
  const NP = 18;
  for (let i = 0; i < NP; i++) {
    const t = 0.05 + (i / (NP - 1)) * 0.95;
    const [bx, by] = bez(shoulder, ctrl, tip, t);
    const jitter = (hash2(i * 7 + (mirrorPalette ? 31 : 3), 17) - 0.5) * 0.22;
    const fan = (t - 0.45) * 0.55; // feathers fan out along the wing
    const ang = bezTangent(shoulder, ctrl, tip, t) + rot + fan + jitter;
    const lenJ = 0.86 + hash2(i * 13 + 5, 41) * 0.3;
    const lenF = (120 + 150 * Math.sin(Math.PI * clamp(0.15 + t * 0.8, 0, 1)) - t * 40) * lenJ;
    const widF = 46 - t * 10;
    const warm = i % 3 === 2;
    // shadow pass: same feather, slightly shorter and nudged toward the
    // trailing side, deep shadowed red (full length poked out as black spikes)
    drawFeather(bx + Math.cos(ang + 1.57) * 5, by + Math.sin(ang + 1.57) * 5, ang, lenF * 0.94, widF, () => [0.26, 0.06, 0.05], { bend: 16, glow: 0 });
    drawFeather(bx, by, ang, lenF, widF, (u, e) => {
      const c = warm ? rampMagenta(u) : ramp(u);
      const dim = 0.58 + 0.42 * (1 - e);
      return [c[0] * dim, c[1] * dim, c[2] * dim];
    }, { bend: 16, glow: 0.35 });
  }
  // secondaries: shorter row, bases pushed toward the trailing side
  const NS = 13;
  for (let i = 0; i < NS; i++) {
    const t = 0.04 + (i / (NS - 1)) * 0.82;
    const [bx, by] = bez(shoulder, ctrl, tip, t);
    const jitter = (hash2(i * 11 + 7, 23) - 0.5) * 0.18;
    const ang = bezTangent(shoulder, ctrl, tip, t) + rot + (t - 0.4) * 0.4 + jitter;
    const ox = bx + Math.cos(ang) * 46;
    const oy = by + Math.sin(ang) * 46;
    drawFeather(ox, oy, ang + 0.12, (108 - t * 25) * (0.9 + hash2(i * 3, 51) * 0.2), 40, (u, e) => {
      const c = ramp(u * 0.85);
      const dim = 0.68 + 0.32 * (1 - e);
      return [c[0] * dim, c[1] * dim, c[2] * dim];
    }, { bend: 12, glow: 0.3 });
  }
  // coverts: small bright scales hugging the leading edge
  const NC = 12;
  for (let i = 0; i < NC; i++) {
    const t = 0.02 + (i / (NC - 1)) * 0.9;
    const [bx, by] = bez(shoulder, ctrl, tip, t);
    const ang = bezTangent(shoulder, ctrl, tip, t) + rot;
    const ox = bx + Math.cos(ang) * 16;
    const oy = by + Math.sin(ang) * 16;
    drawFeather(ox, oy, ang + 0.2, 62 - t * 14, 32, (u) => rampHot(u * 0.7 + 0.25), {
      bend: 6,
      glow: 0.4,
    });
  }
}

// ---------- the phoenix ----------
function renderPhoenix(): void {
  // tail first (behind body): broad curved flame plumes flaring to the sea
  const tailBase: [number, number] = [500, 520];
  const tailAngles = [1.12, 1.3, 1.47, 1.62, 1.78, 1.96, 2.14];
  const tailLens = [225, 265, 300, 315, 295, 260, 215];
  for (let i = 0; i < tailAngles.length; i++) {
    const a = tailAngles[i];
    const bendDir = (i - 3) * 26;
    drawFeather(tailBase[0], tailBase[1], a, tailLens[i], 52 - Math.abs(i - 3) * 4, (u) =>
      i % 2 === 0 ? rampHot(u) : rampMagenta(u * 0.9),
    { bend: bendDir, glow: 0.5 });
  }
  // second, shorter plume layer for fullness
  for (let i = 0; i < 5; i++) {
    const a = 1.28 + i * 0.17;
    drawFeather(tailBase[0] + (i - 2) * 10, tailBase[1] - 6, a, 165 + (2 - Math.abs(i - 2)) * 22, 40, (u) =>
      rampHot(u * 0.9 + 0.08),
    { bend: (i - 2) * 20, glow: 0.45 });
  }

  // wings on a strong diagonal: left tip high, right wing arcing (ctrl lifted
  // well above the shoulder->tip line so it bows instead of lying flat)
  drawWing([482, 430], [300, 235], [118, 148], -2.02, false);
  drawWing([548, 442], [738, 372], [906, 540], 2.18, true);

  // body: one fat tapered shape, near-vertical, slight diagonal lean
  drawFeather(516, 350, 1.62, 218, 132, (u, e) => {
    const c = mixc(EMBER, DEEP_RED, u * 0.8);
    const dim = 1 - e * 0.3;
    return [c[0] * dim, c[1] * dim, c[2] * dim];
  }, { bend: -12, glow: 0.3 });
  // body scale feathers (rows of small bright arcs)
  for (let row = 0; row < 4; row++) {
    for (let k = 0; k < 4; k++) {
      const bx = 478 + k * 24 + (row % 2) * 11;
      const by = 392 + row * 36;
      drawFeather(bx, by, 1.62, 48, 28, (u) => rampHot(0.25 + u * 0.6), { glow: 0.35 });
    }
  }
  // chest core glow — the heart of the bird. Region is far larger than the
  // visible glow and the falloff is steep, so the exp is ~0 at the bounds
  // (pass 1 cut a still-bright falloff and left a hard rectangle).
  for (let y = 272; y < 632; y++) {
    for (let x = 332; x < 692; x++) {
      const dx = x - 512;
      const dy = y - 452;
      const d = Math.sqrt(dx * dx + dy * dy);
      const s = Math.exp(-d / 34) * 0.9 + Math.exp(-d / 15) * 0.95;
      addPx(x, y, WHITE_GOLD, s);
    }
  }

  // head in profile: sleek raptor — elongated skull, long hooked beak,
  // flame crest swept back (pass 1 read as a round cartoon chick)
  const HX = 530;
  const HYH = 336;
  // crest: long plumes raked back over the neck, not a vertical mohawk
  const crest: Array<[number, number, number]> = [
    [-2.95, 96, 12],
    [-2.68, 112, 13],
    [-2.4, 116, 13],
    [-2.12, 104, 12],
    [-1.84, 86, 11],
  ];
  for (const [a, l, w] of crest) {
    drawFeather(HX - 14, HYH - 8, a, l, w, (u) => rampMagenta(u * 0.85 + 0.1), {
      bend: -20,
      glow: 0.55,
    });
  }
  // skull: horizontal ellipse (long axis forward), slightly tilted down
  for (let y = HYH - 30; y <= HYH + 30; y++) {
    for (let x = HX - 44; x <= HX + 46; x++) {
      const dx = x - HX;
      const dy = y - HYH - dx * 0.08; // brow tilts toward the beak
      const e = Math.sqrt((dx * dx) / (44 * 44) + (dy * dy) / (20 * 20));
      const a = clamp((1 - e) * 6 + 0.5, 0, 1);
      if (a <= 0) continue;
      const c = mixc(GOLD, EMBER, clamp(e, 0, 1) * 0.75);
      blendPx(x, y, [c[0] * 1.18, c[1] * 1.1, c[2] * 0.95], a);
    }
  }
  // cheek/throat wedge tying the head into the neck
  drawFeather(HX - 8, HYH + 10, 1.75, 52, 30, (u) => mixc(EMBER, GOLD, u * 0.6), { bend: 6 });
  // beak: long upper mandible with a hooked tip, shorter lower, dark gap
  drawFeather(HX + 26, HYH - 4, 0.06, 84, 15, (u) => mixc(GOLD, WHITE_GOLD, u * 0.8), { bend: 7 });
  drawFeather(HX + 82, HYH + 2, 0.85, 26, 9, (u) => mixc(WHITE_GOLD, GOLD, u), { bend: 4 }); // hook tip
  drawFeather(HX + 24, HYH + 10, 0.42, 52, 11, (u) => mixc(EMBER, GOLD, u), { bend: 3 });
  // eye: fierce almond, dark with a white glint, brow shadow above
  for (let y = HYH - 13; y <= HYH + 1; y++) {
    for (let x = HX + 6; x <= HX + 26; x++) {
      const dx = x - (HX + 15);
      const dy = y - (HYH - 6);
      const e = Math.sqrt((dx * dx) / (6.4 * 6.4) + (dy * dy) / (3.6 * 3.6));
      if (e < 1) blendPx(x, y, [0.04, 0.015, 0.04], clamp((1 - e) * 3 + 0.5, 0, 1));
      if (Math.abs(dx + 2) < 1.3 && Math.abs(dy + 1.5) < 1.1) setPx(x, y, [1.5, 1.45, 1.3]);
    }
  }
}

// ---------- sea: flipped, rippled, dimmed mirror of the scene above ----------
function renderSea(): void {
  // snapshot the sky+phoenix before overwriting sea rows
  const scene = Float32Array.from(buf);
  const sampleScene = (x: number, y: number): RGB => {
    const x0 = clamp(Math.floor(x), 0, W - 2);
    const y0 = clamp(Math.floor(y), 0, H - 2);
    const fx = clamp(x - x0, 0, 1);
    const fy = clamp(y - y0, 0, 1);
    const i00 = (y0 * W + x0) * 3;
    const i10 = i00 + 3;
    const i01 = i00 + W * 3;
    const i11 = i01 + 3;
    const out: RGB = [0, 0, 0];
    for (let k = 0; k < 3; k++) {
      out[k] = lerp(
        lerp(scene[i00 + k], scene[i10 + k], fx),
        lerp(scene[i01 + k], scene[i11 + k], fx),
        fy,
      );
    }
    return out;
  };
  for (let y = HY; y < H; y++) {
    const depth = (y - HY) / (H - HY); // 0 at horizon .. 1 at bottom
    const srcY = HY - (y - HY) * 0.985 - 1;
    const dim = 0.46 - depth * 0.18;
    for (let x = 0; x < W; x++) {
      // gentle warp only — pass 1's ~20px sway broke the reflected wing into
      // detached wavy "worms"; keep it under ~6px so shapes stay readable
      const warp =
        Math.sin(y * 0.11 + x * 0.004) * (0.8 + depth * 2.6) +
        Math.sin(y * 0.031 + 2.0) * (0.5 + depth * 1.8);
      const c = sampleScene(x + warp, srcY);
      // dim + pull hard toward deep indigo (mirror, not mud)
      let r = c[0] * dim + INDIGO[0] * 0.55;
      let g = c[1] * dim + INDIGO[1] * 0.55;
      let b = c[2] * (dim + 0.1) + INDIGO[2] * 0.6;
      // gold light-path under the sun, shimmering toward the viewer
      const pathW = 26 + depth * 130;
      const dxp = Math.abs(x - SUN_X + Math.sin(y * 0.23) * 9);
      const shimmer = 0.55 + 0.45 * Math.sin(y * 1.7 + Math.sin(y * 0.4) * 3 + x * 0.05);
      if (dxp < pathW) {
        const s = (1 - dxp / pathW) * (1 - depth * 0.55) * shimmer;
        r += GOLD[0] * s * 0.5;
        g += GOLD[1] * s * 0.42;
        b += GOLD[2] * s * 0.2;
      }
      setPx(x, y, [r, g, b]);
    }
  }
  // soft glow band straddling the horizon (no hard ruler line)
  for (let k = -3; k <= 3; k++) {
    const s = 0.07 * (1 - Math.abs(k) / 4);
    for (let x = 0; x < W; x++) addPx(x, HY + k, GOLD, s);
  }
}

// ---------- embers / sparks + distant birds ----------
function renderAtmosphere(): void {
  const spark = (cx: number, cy: number, rad: number, col: RGB, strength: number): void => {
    const x0 = clamp(Math.floor(cx - rad * 2), 0, W - 1);
    const x1 = clamp(Math.ceil(cx + rad * 2), 0, W - 1);
    const y0 = clamp(Math.floor(cy - rad * 2), 0, H - 1);
    const y1 = clamp(Math.ceil(cy + rad * 2), 0, H - 1);
    for (let y = y0; y <= y1; y++) {
      for (let x = x0; x <= x1; x++) {
        const dx = x - cx;
        const dy = y - cy;
        const d = Math.sqrt(dx * dx + dy * dy);
        addPx(x, y, col, strength * Math.exp(-(d * d) / (rad * rad)));
      }
    }
  };
  // 165 rising embers, denser low and near the tail column (fewer than pass
  // 1's 240: high-frequency sparks are expensive in the PNG)
  for (let i = 0; i < 165; i++) {
    const nearTail = rng() < 0.45;
    const x = nearTail ? 500 + (rng() * 2 - 1) * 190 : rng() * W;
    const y = rng() * H;
    const rad = 0.8 + rng() * 2.1;
    const bright = 0.25 + rng() * 0.95;
    const col = rng() < 0.25 ? MAGENTA : rng() < 0.5 ? GOLD : EMBER;
    spark(x, y, rad, col, bright);
    // a few get cross flares
    if (rng() < 0.06) {
      const fl = 5 + rng() * 7;
      for (let k = -fl; k <= fl; k++) {
        const s = (1 - Math.abs(k) / fl) * bright * 0.5;
        if (x + k >= 0 && x + k < W) addPx(Math.round(x + k), Math.round(y), col, s);
        if (y + k >= 0 && y + k < H) addPx(Math.round(x), Math.round(y + k), col, s * 0.7);
      }
    }
  }
  // distant birds: tiny dark chevrons for scale
  const birds: Array<[number, number, number]> = [
    [180, 210, 9],
    [228, 188, 7],
    [838, 240, 8],
    [884, 268, 6],
    [716, 150, 7],
    [140, 330, 6],
    [905, 380, 7],
  ];
  for (const [bx, by, s] of birds) {
    for (let k = 0; k <= s; k++) {
      const t = k / s;
      const lx = Math.round(bx - s + k);
      const ly = Math.round(by - Math.sin(t * Math.PI) * s * 0.45 + t * s * 0.2);
      const rx = Math.round(bx + k);
      const ry = Math.round(by - Math.sin(t * Math.PI) * s * 0.45 + (1 - t) * s * 0.2);
      if (lx >= 0 && lx < W && ly >= 0 && ly < H) blendPx(lx, ly, [0.03, 0.02, 0.06], 0.8);
      if (rx >= 0 && rx < W && ry >= 0 && ry < H) blendPx(rx, ry, [0.03, 0.02, 0.06], 0.8);
    }
  }
}

// ---------- bloom: low-res bright blur, added back ----------
function renderBloom(): void {
  const BS = 256;
  const small = new Float32Array(BS * BS * 3);
  const cell = W / BS;
  for (let y = 0; y < BS; y++) {
    for (let x = 0; x < BS; x++) {
      let r = 0;
      let g = 0;
      let b = 0;
      let n = 0;
      for (let sy = 0; sy < cell; sy++) {
        for (let sx = 0; sx < cell; sx++) {
          const i = ((y * cell + sy) * W + x * cell + sx) * 3;
          r += buf[i];
          g += buf[i + 1];
          b += buf[i + 2];
          n++;
        }
      }
      const o = (y * BS + x) * 3;
      small[o] = r / n;
      small[o + 1] = g / n;
      small[o + 2] = b / n;
    }
  }
  // two separable box blurs, radius 5
  const tmp = new Float32Array(small.length);
  for (let pass = 0; pass < 2; pass++) {
    const R = 5;
    for (let y = 0; y < BS; y++) {
      for (let x = 0; x < BS; x++) {
        let r = 0;
        let g = 0;
        let b = 0;
        let n = 0;
        for (let k = -R; k <= R; k++) {
          const xx = clamp(x + k, 0, BS - 1);
          const i = (y * BS + xx) * 3;
          r += small[i];
          g += small[i + 1];
          b += small[i + 2];
          n++;
        }
        const o = (y * BS + x) * 3;
        tmp[o] = r / n;
        tmp[o + 1] = g / n;
        tmp[o + 2] = b / n;
      }
    }
    for (let y = 0; y < BS; y++) {
      for (let x = 0; x < BS; x++) {
        let r = 0;
        let g = 0;
        let b = 0;
        let n = 0;
        for (let k = -R; k <= R; k++) {
          const yy = clamp(y + k, 0, BS - 1);
          const i = (yy * BS + x) * 3;
          r += tmp[i];
          g += tmp[i + 1];
          b += tmp[i + 2];
          n++;
        }
        const o = (y * BS + x) * 3;
        small[o] = r / n;
        small[o + 1] = g / n;
        small[o + 2] = b / n;
      }
    }
  }
  // add back, gated on local brightness so only highlights bloom
  for (let y = 0; y < H; y++) {
    for (let x = 0; x < W; x++) {
      const gx = clamp((x / W) * (BS - 1), 0, BS - 2);
      const gy = clamp((y / H) * (BS - 1), 0, BS - 2);
      const x0 = Math.floor(gx);
      const y0 = Math.floor(gy);
      const fx = gx - x0;
      const fy = gy - y0;
      const i00 = (y0 * BS + x0) * 3;
      const i = (y * W + x) * 3;
      for (let k = 0; k < 3; k++) {
        const top = lerp(small[i00 + k], small[i00 + 3 + k], fx);
        const bot = lerp(small[i00 + BS * 3 + k], small[i00 + BS * 3 + 3 + k], fx);
        const bloom = lerp(top, bot, fy);
        const lum = buf[i] * 0.4 + buf[i + 1] * 0.35 + buf[i + 2] * 0.25;
        const gate = clamp((lum - 0.5) * 1.6, 0, 1);
        buf[i + k] += bloom * 0.55 * gate;
      }
    }
  }
}

// ---------- finish: vignette, tonemap, whisper of grain ----------
function finish(): Uint8Array {
  const out = new Uint8Array(W * H * 3);
  const cx = W / 2;
  const cy = H / 2;
  const maxD = Math.sqrt(cx * cx + cy * cy);
  for (let y = 0; y < H; y++) {
    for (let x = 0; x < W; x++) {
      const i = (y * W + x) * 3;
      const dx = x - cx;
      const dy = y - cy;
      const d = Math.sqrt(dx * dx + dy * dy) / maxD;
      const vig = 1 - 0.42 * smooth(clamp((d - 0.45) / 0.55, 0, 1));
      const grain = (hash2(x * 7 + 13, y * 7 + 91) - 0.5) * 2 * (0.9 / 255);
      // gentle shoulder only (was 0.32 + gamma 0.88, which washed everything
      // to pastel); then a saturation push to restore warm/cool tension
      const tm: RGB = [0, 0, 0];
      for (let k = 0; k < 3; k++) {
        let c = buf[i + k] * vig;
        c = c / (1 + c * 0.14);
        tm[k] = Math.pow(clamp(c, 0, 1), 1.02);
      }
      const lum = tm[0] * 0.35 + tm[1] * 0.45 + tm[2] * 0.2;
      for (let k = 0; k < 3; k++) {
        const c = clamp(lum + (tm[k] - lum) * 1.38, 0, 1);
        // quantise to steps of 3: keeps smooth gradients cheap to deflate
        const q = Math.round(((c + grain) * 255) / 3) * 3;
        out[i + k] = clamp(q, 0, 255);
      }
    }
  }
  return out;
}

// ---------- main ----------
function main(): void {
  const t0 = performance.now();
  renderSky();
  renderSun();
  renderPhoenix();
  renderSea();
  renderAtmosphere();
  renderBloom();
  const rgb = finish();
  const png = encodePNG(rgb);
  const outDir = process.env.MAKEFUN_OUTPUT_DIR || "/output";
  mkdirSync(outDir, { recursive: true });
  writeFileSync(join(outDir, "entry.png"), png);
  const sha256 = createHash("sha256").update(png).digest("hex");
  const seconds = Math.round(((performance.now() - t0) / 1000) * 1000) / 1000;
  console.log(
    JSON.stringify({ width: W, height: H, bytes: png.length, sha256, seconds }),
  );
}
main();
