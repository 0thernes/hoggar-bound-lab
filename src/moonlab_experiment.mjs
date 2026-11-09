/*
 * moonlab_experiment.mjs - the state-independent contextuality experiment, run on Tsotchke's
 * Moonlab (a classical state-vector simulator; the prebuilt WebAssembly engine v1.2.1 vendored in
 * third_party/moonlab).  Random numbers come from Tsotchke's quantum_rng (a classical
 * "quantum-inspired" mixer) through build/qrng_stream.exe.  Nothing here is a hardware quantum
 * measurement: it is a faithful simulation of what quantum mechanics predicts.
 *
 * Experiments
 *   E1  Prepare the Hoggar fiducial on 3 simulated qubits, read all 63 Pauli expectation values,
 *       take signs -> a noncontextual assignment; count violated contexts (prediction: exactly 63).
 *   E2  Same with the realified Hoggar state on 4 simulated qubits (prediction: flat +-1/3 on the
 *       135 real observables, 0 on the 120 imaginary ones, exactly 315 violated contexts of Q+(7,2)).
 *   E3  Ideal sequential measurement of every context on random states (prediction: 100% agreement
 *       with the operator sign, for every state).
 *   E4  The same with Pauli noise between measurements: measured success fraction versus the
 *       classical ceilings.
 *
 * usage: node src/moonlab_experiment.mjs [seed]
 * Geometry (points, lines, signs) is re-implemented here independently of src/hoggar.c.
 */
import { createRequire } from 'node:module';
import { execFileSync } from 'node:child_process';
import { writeFileSync, readFileSync, existsSync, mkdirSync } from 'node:fs';
import { fileURLToPath } from 'node:url';
import path from 'node:path';

const here = path.dirname(fileURLToPath(import.meta.url));
const root = path.resolve(here, '..');
const require = createRequire(import.meta.url);
const SEED = Number(process.argv[2] ?? 20261109);

/* ------------------------------------------------------------------ randomness */
class Stream {
  constructor(seed) { this.seed = seed; this.buf = Buffer.alloc(0); this.at = 0; this.chunk = 0; this.used = 0; }
  refill() {
    // each refill uses a fresh derived seed so the stream never repeats
    const hex = execFileSync(path.join(root, 'build', 'qrng_stream.exe'),
      [String(this.seed + 1000003 * this.chunk), String(1 << 18)], { maxBuffer: 1 << 22 }).toString();
    this.buf = Buffer.from(hex, 'hex'); this.at = 0; this.chunk++;
  }
  u32() { if (this.at + 4 > this.buf.length) this.refill(); const x = this.buf.readUInt32LE(this.at); this.at += 4; this.used += 4; return x; }
  unit() { return (this.u32() >>> 8) / 16777216; }
  below(m) { return Math.floor(this.unit() * m); }
  shuffle(arr) { for (let i = arr.length - 1; i > 0; i--) { const j = this.below(i + 1); [arr[i], arr[j]] = [arr[j], arr[i]]; } return arr; }
}

/* ------------------------------------------------------------------ geometry (independent implementation) */
const pop = (x) => { let c = 0; while (x) { x &= x - 1; c++; } return c; };
function geometry(N, type = 'f') {
  const D = 1 << N, n = 1 << (2 * N);
  const A = (v) => v & (D - 1), C = (v) => v >> N;
  const member = (v) => {
    if (v === 0) return false;
    const y = pop(A(v) & C(v)) & 1;
    if (type === 'f') return true;
    if (type === 'h') return y === 0;
    const top = ((A(v) >> (N - 1)) & 1) ^ ((C(v) >> (N - 1)) & 1);
    return (y ^ top) === 0;
  };
  const commute = (u, v) => ((pop(A(u) & C(v)) + pop(C(u) & A(v))) & 1) === 0;
  const sign = (u, v) => {
    const k = (pop(A(u) & C(u)) + pop(A(v) & C(v)) + 2 * pop(C(u) & A(v)) + 3 * pop((A(u) ^ A(v)) & (C(u) ^ C(v)))) & 3;
    return k === 0 ? 1 : -1;
  };
  const pts = []; for (let v = 1; v < n; v++) if (member(v)) pts.push(v);
  const inS = new Uint8Array(n); for (const v of pts) inS[v] = 1;
  const lines = [];
  for (const u of pts) for (const v of pts) {
    const w = u ^ v;
    if (v > u && w > v && inS[w] && commute(u, v)) lines.push([u, v, w, sign(u, v)]);
  }
  return { N, D, n, A, C, pts, inS, lines, type };
}
const countViolations = (g, f) => g.lines.reduce((acc, [u, v, w, s]) => acc + (f[u] * f[v] * f[w] !== s ? 1 : 0), 0);

/* ------------------------------------------------------------------ Moonlab wrapper */
const Moonlab = await require(path.join(root, 'third_party', 'moonlab', 'moonlab.js'))({ print: () => {}, printErr: () => {} });
const STRUCT = 256;
function newState(N) {
  const p = Moonlab._malloc(STRUCT);
  Moonlab.HEAPU8.fill(0, p, p + STRUCT);
  const rc = Moonlab._quantum_state_init(p, N);
  if (rc !== 0) throw new Error('quantum_state_init failed: ' + rc);
  return p;
}
const freeState = (p) => { Moonlab._quantum_state_free(p); Moonlab._free(p); };
function cloneState(p) {
  const q = Moonlab._malloc(STRUCT);
  Moonlab.HEAPU8.fill(0, q, q + STRUCT);
  const rc = Moonlab._quantum_state_clone(q, p);
  if (rc !== 0) throw new Error('quantum_state_clone failed: ' + rc);
  return q;
}
const ampPtr = (p) => Moonlab.HEAPU32[(p + 8) >> 2];
function setAmplitudes(p, re, im) {
  const base = ampPtr(p) >> 3;
  let norm = 0; for (let k = 0; k < re.length; k++) norm += re[k] * re[k] + im[k] * im[k];
  norm = Math.sqrt(norm);
  for (let k = 0; k < re.length; k++) { Moonlab.HEAPF64[base + 2 * k] = re[k] / norm; Moonlab.HEAPF64[base + 2 * k + 1] = im[k] / norm; }
}
function getAmplitudes(p, D) {
  const base = ampPtr(p) >> 3; const out = [];
  for (let k = 0; k < D; k++) out.push([Moonlab.HEAPF64[base + 2 * k], Moonlab.HEAPF64[base + 2 * k + 1]]);
  return out;
}
/* rotate the eigenbasis of the Pauli string (a,c) onto Z of one support qubit; returns that qubit */
function toZ(p, N, a, c) {
  let t = -1; let gates = 0;
  for (let j = 0; j < N; j++) {
    const x = (a >> j) & 1, z = (c >> j) & 1;
    if (!x && !z) continue;
    if (x && z) { Moonlab._gate_s_dagger(p, j); Moonlab._gate_hadamard(p, j); gates += 2; }
    else if (x) { Moonlab._gate_hadamard(p, j); gates++; }
    if (t < 0) t = j;
  }
  for (let j = 0; j < N; j++) if (j !== t && (((a | c) >> j) & 1)) { Moonlab._gate_cnot(p, j, t); gates++; }
  return [t, gates];
}
function fromZ(p, N, a, c, t) {
  for (let j = N - 1; j >= 0; j--) if (j !== t && (((a | c) >> j) & 1)) Moonlab._gate_cnot(p, j, t);
  for (let j = 0; j < N; j++) {
    const x = (a >> j) & 1, z = (c >> j) & 1;
    if (x && z) { Moonlab._gate_hadamard(p, j); Moonlab._gate_s(p, j); }
    else if (x) Moonlab._gate_hadamard(p, j);
  }
}
/* projective measurement of the Pauli observable (a,c); returns +1 / -1 and collapses the state */
let gateCount = 0, measCount = 0;
function measurePauli(p, N, a, c, r) {
  const [t, g] = toZ(p, N, a, c);
  const bit = Moonlab._measurement_single_qubit(p, t, r);
  fromZ(p, N, a, c, t);
  gateCount += 2 * g; measCount++;
  return bit ? -1 : 1;
}
/* expectation value <psi| P |psi> without disturbing p */
function expectPauli(p, N, a, c) {
  const q = cloneState(p);
  const [t] = toZ(q, N, a, c);
  const e = Moonlab._measurement_expectation_z(q, t);
  freeState(q);
  return e;
}
function randomState(N, rnd, layers = 6) {
  const p = newState(N);
  for (let l = 0; l < layers; l++) {
    for (let j = 0; j < N; j++) { Moonlab._gate_ry(p, j, 2 * Math.PI * rnd.unit()); Moonlab._gate_rz(p, j, 2 * Math.PI * rnd.unit()); }
    for (let j = 0; j + 1 < N; j++) Moonlab._gate_cnot(p, j, j + 1);
    if (N > 2) Moonlab._gate_cnot(p, N - 1, 0);
  }
  return p;
}
function applyRandomPauliNoise(p, N, rnd, perr) {
  for (let j = 0; j < N; j++) if (rnd.unit() < perr) {
    const k = rnd.below(3);
    if (k === 0) Moonlab._gate_pauli_x(p, j); else if (k === 1) Moonlab._gate_pauli_y(p, j); else Moonlab._gate_pauli_z(p, j);
  }
}

/* ------------------------------------------------------------------ helpers */
function writeAssignment(g, f, viol, file) {
  let hex = '';
  for (let nib = g.n / 4 - 1; nib >= 0; nib--) {
    let x = 0; for (let b = 0; b < 4; b++) { const v = nib * 4 + b; if (g.inS[v] && f[v] < 0) x |= 1 << b; }
    hex += x.toString(16);
  }
  writeFileSync(file, `${g.N} ${g.type} ${viol}\n${hex}\n`);
}
function readAssignment(g, file) {
  const [, hex] = readFileSync(file, 'utf8').trim().split('\n');
  const f = new Int8Array(g.n).fill(1);
  for (let k = 0; k < hex.length; k++) { const x = parseInt(hex[k], 16); const nib = hex.length - 1 - k; for (let b = 0; b < 4; b++) if (x & (1 << b)) f[nib * 4 + b] = -1; }
  return f;
}
const results = { seed: SEED, moonlab_abi: Moonlab._moonlab_abi_version ? Moonlab._moonlab_abi_version() : null, experiments: {} };
const log = (...a) => console.log(...a);
const rnd = new Stream(SEED);
mkdirSync(path.join(root, 'results'), { recursive: true });
mkdirSync(path.join(root, 'data', 'witness'), { recursive: true });

/* ------------------------------------------------------------------ E0: self-test of the measurement primitive */
{
  const N = 3, g = geometry(N), p = randomState(N, rnd);
  let maxdev = 0, repeatOk = true;
  // compare Moonlab expectation with a direct state-vector evaluation in JS
  const amp = getAmplitudes(p, g.D);
  for (const v of g.pts) {
    const a = g.A(v), c = g.C(v), k = pop(a & c) & 3;
    let re = 0, im = 0;   // sum_x conj(psi[x^a]) * (-1)^{c.x} psi[x], times i^k
    for (let x = 0; x < g.D; x++) {
      const s = pop(c & x) & 1 ? -1 : 1, [br, bi] = amp[x ^ a], [kr, ki] = amp[x];
      re += s * (br * kr + bi * ki); im += s * (br * ki - bi * kr);
    }
    const ph = [[1, 0], [0, 1], [-1, 0], [0, -1]][k];
    const direct = re * ph[0] - im * ph[1];
    maxdev = Math.max(maxdev, Math.abs(direct - expectPauli(p, N, a, c)));
  }
  for (let trial = 0; trial < 200; trial++) {
    const v = g.pts[rnd.below(g.pts.length)];
    const o1 = measurePauli(p, N, g.A(v), g.C(v), rnd.unit());
    const o2 = measurePauli(p, N, g.A(v), g.C(v), rnd.unit());
    if (o1 !== o2) repeatOk = false;
  }
  freeState(p);
  results.experiments.E0 = { max_expectation_deviation: maxdev, repeated_measurement_consistent: repeatOk };
  log(`E0 self-test: |Moonlab <P> - direct <P>| <= ${maxdev.toExponential(2)}; repeated measurements agree: ${repeatOk}`);
}

/* ------------------------------------------------------------------ E1: Hoggar fiducial -> optimal assignment */
{
  const N = 3, g = geometry(N), p = newState(N);
  const re = [-1, 1, 1, 1, 1, 1, 1, 1], im = [2, 0, 0, 0, 0, 0, 0, 0];
  setAmplitudes(p, re, im);
  const f = new Int8Array(g.n).fill(1); let maxdev = 0;
  for (const v of g.pts) { const e = expectPauli(p, N, g.A(v), g.C(v)); maxdev = Math.max(maxdev, Math.abs(Math.abs(e) - 1 / 3)); f[v] = e >= 0 ? 1 : -1; }
  const viol = countViolations(g, f);
  const deg = new Map(); for (const [u, v, w, s] of g.lines) if (f[u] * f[v] * f[w] !== s) for (const x of [u, v, w]) deg.set(x, (deg.get(x) ?? 0) + 1);
  writeAssignment(g, f, viol, path.join(root, 'data', 'witness', 'n3_f_hoggar_moonlab.txt'));
  freeState(p);
  results.experiments.E1 = { contexts: g.lines.length, max_deviation_from_one_third: maxdev, violated: viol, points_on_violated_lines: deg.size, violated_lines_per_point: [...new Set(deg.values())] };
  log(`E1 Hoggar state on Moonlab: 63 Pauli expectations = +-1/3 (max dev ${maxdev.toExponential(2)}); sign assignment violates ${viol} of ${g.lines.length} contexts; every point on ${[...new Set(deg.values())]} violated lines`);
}

/* ------------------------------------------------------------------ E2: realified Hoggar on 4 simulated qubits */
{
  const N = 4, gh = geometry(N, 'h'), gf = geometry(N, 'f'), p = newState(N);
  // C^8 -> R^16: |psi_R> = Re(psi) (x) |0> + Im(psi) (x) |1> on the extra (most significant) qubit
  const re = [-1, 1, 1, 1, 1, 1, 1, 1, 2, 0, 0, 0, 0, 0, 0, 0], im = new Array(16).fill(0);
  setAmplitudes(p, re, im);
  const f = new Int8Array(gf.n).fill(1); let devReal = 0, devImag = 0;
  for (const v of gf.pts) {
    const e = expectPauli(p, N, gf.A(v), gf.C(v));
    if (gh.inS[v]) { devReal = Math.max(devReal, Math.abs(Math.abs(e) - 1 / 3)); f[v] = e >= 0 ? 1 : -1; }
    else devImag = Math.max(devImag, Math.abs(e));
  }
  const viol = countViolations(gh, f);
  const deg = new Map(); for (const [u, v, w, s] of gh.lines) if (f[u] * f[v] * f[w] !== s) for (const x of [u, v, w]) deg.set(x, (deg.get(x) ?? 0) + 1);
  writeAssignment(gh, f, viol, path.join(root, 'data', 'witness', 'n4_h_hoggar_moonlab.txt'));
  freeState(p);
  results.experiments.E2 = { contexts: gh.lines.length, max_dev_real: devReal, max_abs_imaginary: devImag, violated: viol, violated_lines_per_point: [...new Set(deg.values())] };
  log(`E2 realified Hoggar on Moonlab: 135 real observables = +-1/3 (dev ${devReal.toExponential(2)}), 120 imaginary = 0 (max ${devImag.toExponential(2)}); violates ${viol} of ${gh.lines.length} contexts of Q+(7,2); every point on ${[...new Set(deg.values())]} violated lines`);
}

/* ------------------------------------------------------------------ E3: ideal state-independent test, every context */
results.experiments.E3 = [];
for (const N of [2, 3, 4]) {
  const g = geometry(N);
  for (let rep = 0; rep < 3; rep++) {
    const p = randomState(N, rnd);
    const order = rnd.shuffle(g.lines.map((_, i) => i));
    let ok = 0; gateCount = 0; measCount = 0;
    for (const i of order) {
      const [u, v, w, s] = g.lines[i];
      const o = [u, v, w].map((x) => measurePauli(p, N, g.A(x), g.C(x), rnd.unit()));
      if (o[0] * o[1] * o[2] === s) ok++;
    }
    freeState(p);
    results.experiments.E3.push({ N, rep, contexts: g.lines.length, agree: ok, gates: gateCount, measurements: measCount });
    log(`E3 N=${N} run ${rep}: ${ok}/${g.lines.length} contexts give the quantum sign (chi = ${2 * ok - g.lines.length} of ${g.lines.length}); ${gateCount} gates, ${measCount} projective measurements`);
  }
}

/* ------------------------------------------------------------------ E4: noisy benchmark against classical ceilings */
const ceilings = {   // success-probability ceilings for a noncontextual model: 1 - d/L
  2: { L: 15, best_known_d: 3, proven_d: 3 },
  3: { L: 315, best_known_d: 63, proven_d: 63 },
  4: { L: 5355, best_known_d: 1575, proven_d: 1451 },
};
results.experiments.E4 = [];
for (const N of [2, 3, 4]) {
  const g = geometry(N), shots = N === 4 ? 4000 : 3000;
  const fbestFile = path.join(root, 'data', 'witness', N === 4 ? 'n4_f.txt' : 'n3_f_hoggar_moonlab.txt');
  const fbest = N >= 3 && existsSync(fbestFile) ? readAssignment(g, fbestFile) : null;
  for (const perr of [0, 0.01, 0.02, 0.05, 0.1, 0.2]) {
    const p = randomState(N, rnd);
    let ok = 0, okClassical = 0;
    for (let sh = 0; sh < shots; sh++) {
      const [u, v, w, s] = g.lines[rnd.below(g.lines.length)];
      let prod = 1;
      for (const x of [u, v, w]) { applyRandomPauliNoise(p, N, rnd, perr); prod *= measurePauli(p, N, g.A(x), g.C(x), rnd.unit()); }
      if (prod === s) ok++;
      if (fbest && fbest[u] * fbest[v] * fbest[w] === s) okClassical++;
    }
    freeState(p);
    const c = ceilings[N];
    const row = { N, noise_per_qubit_per_measurement: perr, shots, quantum_success: ok / shots,
      classical_best_known_on_same_contexts: fbest ? okClassical / shots : null,
      ceiling_best_known: 1 - c.best_known_d / c.L, ceiling_proven: 1 - c.proven_d / c.L,
      five_sigma: 5 * Math.sqrt(0.25 / shots) };
    row.violates_proven_ceiling = row.quantum_success - row.five_sigma > row.ceiling_proven;
    results.experiments.E4.push(row);
    log(`E4 N=${N} noise=${perr}: simulated quantum success ${(ok / shots).toFixed(4)} | proven classical ceiling ${row.ceiling_proven.toFixed(4)} | best classical model on same contexts ${fbest ? (okClassical / shots).toFixed(4) : 'n/a'} | violates (5 sigma): ${row.violates_proven_ceiling}`);
  }
}
results.random_bytes_used = rnd.used;
writeFileSync(path.join(root, 'results', 'moonlab_experiment.json'), JSON.stringify(results, null, 1));
log(`random bytes drawn from quantum_rng stream: ${rnd.used}`);
