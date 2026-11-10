/*
 * moonlab_saturated.mjs - the configurations on which the spectral floor is attained, on Tsotchke's
 * Moonlab (a classical state-vector simulator; prebuilt WebAssembly engine vendored in
 * third_party/moonlab), with random numbers from Tsotchke's quantum_rng (a classical mixer) through
 * build/qrng_stream.  Nothing here is a hardware measurement.
 *
 *   S1  Prepare eight states: six by their amplitudes, and the two phase states Phi5 and Phi7 by running
 *       their circuits (Hadamards, controlled-S and CCZ gates) on Moonlab.  Read every Pauli expectation
 *       value through Moonlab's gates.  Check that the nonzero ones have one modulus, that their support
 *       and signs are the masks of data/flat/, and recount contexts and violated contexts from the
 *       simulator's numbers.
 *   S2  Measure every context of the four-qubit pivot configuration (1095) and of the two five-qubit
 *       configurations (10880 each) sequentially on random states: the three outcomes must multiply to
 *       the operator sign every time, although no assignment of values can do that for more than
 *       1020 (resp. 10400) contexts.  For the seven-qubit configuration (2824192 contexts) a random
 *       sample of 30000 contexts is measured; --full7 measures all of them.
 *   S3  The same with Pauli noise, against the exact classical ceilings 1 - d/L.
 *
 * usage: node src/moonlab_saturated.mjs [seed] [--full7]
 * The geometry is re-implemented here; it shares no code with the C, Python, Eshkol or Lean versions.
 */
import { createRequire } from 'node:module';
import { execFileSync } from 'node:child_process';
import { writeFileSync, readFileSync, existsSync, mkdirSync } from 'node:fs';
import { fileURLToPath } from 'node:url';
import path from 'node:path';

const here = path.dirname(fileURLToPath(import.meta.url));
const root = path.resolve(here, '..');
const require = createRequire(import.meta.url);
const ARGS = process.argv.slice(2);
const FULL7 = ARGS.includes('--full7');
const SEED = Number(ARGS.find((a) => /^[0-9]+$/.test(a)) ?? 20261110);
let failures = 0;
const log = (...a) => console.log(...a);
const check = (ok, msg) => { log(`${ok ? 'PASS' : 'FAIL'}  ${msg}`); if (!ok) failures++; return ok; };

/* ------------------------------------------------------------------ randomness (quantum_rng stream) */
class Stream {
  constructor(seed) { this.seed = seed; this.buf = Buffer.alloc(0); this.at = 0; this.chunk = 0; this.used = 0; }
  refill() {
    const exe = ['qrng_stream.exe', 'qrng_stream'].map((f) => path.join(root, 'build', f)).find((f) => existsSync(f));
    if (!exe) throw new Error('build/qrng_stream is missing: run scripts/build.sh first');
    const hex = execFileSync(exe, [String(this.seed + 1000003 * this.chunk), String(1 << 18)], { maxBuffer: 1 << 22 }).toString();
    this.buf = Buffer.from(hex, 'hex'); this.at = 0; this.chunk++;
  }
  u32() { if (this.at + 4 > this.buf.length) this.refill(); const x = this.buf.readUInt32LE(this.at); this.at += 4; this.used += 4; return x; }
  unit() { return (this.u32() >>> 8) / 16777216; }
  below(m) { return Math.floor(this.unit() * m); }
  shuffle(arr) { for (let i = arr.length - 1; i > 0; i--) { const j = this.below(i + 1); [arr[i], arr[j]] = [arr[j], arr[i]]; } return arr; }
}

/* ------------------------------------------------------------------ geometry of an arbitrary set of observables */
const pop = (x) => { let c = 0; while (x) { x &= x - 1; c++; } return c; };
function configuration(N, pts) {
  const D = 1 << N, n = 1 << (2 * N);
  const A = (v) => v & (D - 1), C = (v) => v >> N;
  const commute = (u, v) => ((pop(A(u) & C(v)) + pop(C(u) & A(v))) & 1) === 0;
  const sign = (u, v) => {
    const k = (pop(A(u) & C(u)) + pop(A(v) & C(v)) + 2 * pop(C(u) & A(v)) + 3 * pop((A(u) ^ A(v)) & (C(u) ^ C(v)))) & 3;
    return k === 0 ? 1 : -1;
  };
  const inS = new Uint8Array(n); for (const v of pts) inS[v] = 1;
  const lines = [];
  for (const u of pts) for (const v of pts) {
    const w = u ^ v;
    if (v > u && w > v && inS[w] && commute(u, v)) lines.push([u, v, w, sign(u, v)]);
  }
  return { N, D, n, A, C, pts, inS, lines };
}
const violations = (g, f) => g.lines.reduce((acc, [u, v, w, s]) => acc + (f[u] * f[v] * f[w] !== s ? 1 : 0), 0);
const maskOf = (vs) => vs.reduce((m, v) => m | (1n << BigInt(v)), 0n);

/* ------------------------------------------------------------------ Moonlab wrapper */
const Moonlab = await require(path.join(root, 'third_party', 'moonlab', 'moonlab.js'))({ print: () => {}, printErr: () => {} });
const STRUCT = 256;
function newState(N) {
  const p = Moonlab._malloc(STRUCT);
  Moonlab.HEAPU8.fill(0, p, p + STRUCT);
  if (Moonlab._quantum_state_init(p, N) !== 0) throw new Error('quantum_state_init failed');
  return p;
}
const freeState = (p) => { Moonlab._quantum_state_free(p); Moonlab._free(p); };
function cloneState(p) {
  const q = Moonlab._malloc(STRUCT);
  Moonlab.HEAPU8.fill(0, q, q + STRUCT);
  if (Moonlab._quantum_state_clone(q, p) !== 0) throw new Error('quantum_state_clone failed');
  return q;
}
function setAmplitudes(p, amp) {
  const base = Moonlab.HEAPU32[(p + 8) >> 2] >> 3;
  const norm = Math.sqrt(amp.reduce((s, [re, im]) => s + re * re + im * im, 0));
  amp.forEach(([re, im], k) => { Moonlab.HEAPF64[base + 2 * k] = re / norm; Moonlab.HEAPF64[base + 2 * k + 1] = im / norm; });
}
function toZ(p, N, a, c) {
  let t = -1, gates = 0;
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
let gateCount = 0, measCount = 0;
function measurePauli(p, N, a, c, r) {
  const [t, g] = toZ(p, N, a, c);
  const bit = Moonlab._measurement_single_qubit(p, t, r);
  fromZ(p, N, a, c, t);
  gateCount += 2 * g; measCount++;
  return bit ? -1 : 1;
}
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
function pauliNoise(p, N, rnd, perr) {
  for (let j = 0; j < N; j++) if (rnd.unit() < perr) {
    const k = rnd.below(3);
    if (k === 0) Moonlab._gate_pauli_x(p, j); else if (k === 1) Moonlab._gate_pauli_y(p, j); else Moonlab._gate_pauli_z(p, j);
  }
}

/* ------------------------------------------------------------------ the six states (amplitudes of |x>, bit k of x = qubit k) */
const one = [1, 0], I = [0, 1], zero = [0, 0];
const mul = ([a, b], [c, d]) => [a * c - b * d, a * d + b * c];
const neg = ([a, b]) => [-a, -b];
const bent = [3, 7, 11, 12, 13, 14];             // support of x0 x1 + x2 x3
const a1 = [-1, -2], a2 = [2, -1], a3 = [5, 0], a4 = [-3, 4];
const STATES = [
  { name: 'lly', N: 2, amp: [I, I, I, one], expect: [12, 8, 0] },
  { name: 'ccz', N: 3, amp: Array.from({ length: 8 }, (_, x) => [x === 7 ? -1 : 1, 0]), expect: [28, 56, 0] },
  { name: 'hoggar', N: 3, amp: [[-1, 2], one, one, one, one, one, one, one], expect: [63, 315, 63] },
  { name: 'quadric', N: 4, amp: Array.from({ length: 16 }, (_, x) => [x === 0 ? -3 : 1, 0]), expect: [135, 1575, 315] },
  { name: 'pivot', N: 4, amp: Array.from({ length: 16 }, (_, x) => (bent.includes(x) ? (x === 14 ? I : one) : zero)), expect: [135, 1095, 75] },
  { name: 'cieslinski5', N: 5, amp: [a1, neg(a2), a1, neg(a2), neg(a1), neg(a2), neg(a1), a2, mul(I, a3), a1, a2, a3, a2, a4, neg(a2), a3,
      a2, a3, neg(a2), neg(a1), a2, neg(a4), neg(a2), neg(a1), a1, neg(mul(I, a3)), neg(a1), a2, neg(a3), a2, neg(a1), neg(a2)], expect: [496, 10880, 480] },
];

/* the two phase states of Section 5.3, as circuits on |0...0>: H on every qubit, CS = controlled phase pi/2,
   CCZ = H Toffoli H on the target */
const PHASE = [
  { name: 'phase5', N: 5, cs: [[0, 1], [1, 3], [2, 4]], ccz: [[0, 1, 4], [0, 2, 3]], expect: [496, 10880, 480] },
  { name: 'phase7', N: 7, cs: [[0, 1], [2, 3], [4, 5]],
    ccz: [[0, 1, 2], [0, 3, 5], [1, 2, 4], [0, 4, 6], [0, 5, 6], [1, 3, 6], [2, 3, 6], [2, 5, 6]], expect: [8128, 2824192, 729344] },
];
function runCircuit(st) {
  const p = newState(st.N);
  let gates = 0;
  for (let j = 0; j < st.N; j++) { Moonlab._gate_hadamard(p, j); gates++; }
  for (const [j, k] of st.cs) { Moonlab._gate_cphase(p, j, k, Math.PI / 2); gates++; }
  for (const [j, k, l] of st.ccz) { Moonlab._gate_hadamard(p, l); Moonlab._gate_toffoli(p, j, k, l); Moonlab._gate_hadamard(p, l); gates += 3; }
  return [p, gates];
}
function circuitDeviation(p, st) {
  const D = 1 << st.N, base = Moonlab.HEAPU32[(p + 8) >> 2] >> 3, r = 1 / Math.sqrt(D);
  let dev = 0;
  for (let x = 0; x < D; x++) {
    const b = (j) => (x >> j) & 1;
    let q = 0;
    for (const [j, k] of st.cs) q += b(j) * b(k);
    for (const [j, k, l] of st.ccz) q += 2 * b(j) * b(k) * b(l);
    const want = [[r, 0], [0, r], [-r, 0], [0, -r]][q & 3];
    dev = Math.max(dev, Math.abs(Moonlab.HEAPF64[base + 2 * x] - want[0]), Math.abs(Moonlab.HEAPF64[base + 2 * x + 1] - want[1]));
  }
  return dev;
}

const rnd = new Stream(SEED);
const results = { seed: SEED, S1: [], S2: [], S3: [] };
mkdirSync(path.join(root, 'results'), { recursive: true });
const configs = {};

/* ------------------------------------------------------------------ S1 */
for (const st of [...STATES, ...PHASE]) {
  const { N, name } = st, n = 1 << (2 * N), D = 1 << N;
  let p;
  if (st.amp) { p = newState(N); setAmplitudes(p, st.amp); }
  else {
    let gates; [p, gates] = runCircuit(st);
    const dev = circuitDeviation(p, st);
    check(dev < 1e-12, `S1 ${name}: the circuit (${N} H, ${st.cs.length} CS, ${st.ccz.length} CCZ; ${gates} Moonlab gates) prepares the state with amplitudes i^q / sqrt(D) (deviation ${dev.toExponential(1)})`);
  }
  const e = new Float64Array(n);
  for (let v = 1; v < n; v++) e[v] = expectPauli(p, N, v & (D - 1), v >> N);
  freeState(p);
  const pts = []; let mu = 0;
  for (let v = 1; v < n; v++) if (Math.abs(e[v]) > 1e-9) { pts.push(v); mu = Math.max(mu, Math.abs(e[v])); }
  let dev = 0; for (const v of pts) dev = Math.max(dev, Math.abs(Math.abs(e[v]) - mu));
  let zeroDev = 0; for (let v = 1; v < n; v++) if (Math.abs(e[v]) <= 1e-9) zeroDev = Math.max(zeroDev, Math.abs(e[v]));
  const g = configuration(N, pts);
  const f = new Int8Array(n).fill(1); for (const v of pts) f[v] = e[v] >= 0 ? 1 : -1;
  const viol = violations(g, f);
  const muExact = Math.sqrt((D - 1) / pts.length);
  const beta = ((D - 1) * (D - 2)) / (6 * muExact ** 3);
  const [, maskHex, negHex] = readFileSync(path.join(root, 'data', 'flat', `n${N}_${name}.txt`), 'utf8').trim().split('\n');
  const sameSupport = maskOf(pts) === BigInt('0x' + maskHex);
  const sameSigns = maskOf(pts.filter((v) => f[v] < 0)) === BigInt('0x' + negHex);
  check(dev < 1e-12 && zeroDev < 1e-12 && Math.abs(mu - muExact) < 1e-12,
    `S1 ${name}: on Moonlab the ${pts.length} nonzero Pauli expectation values all have modulus ${mu.toFixed(6)} = sqrt((D-1)/|S|) (deviation ${dev.toExponential(1)})`);
  check(sameSupport && sameSigns, `S1 ${name}: support and signs read from the simulator equal the masks in data/flat/n${N}_${name}.txt`);
  check(pts.length === st.expect[0] && g.lines.length === st.expect[1] && viol === st.expect[2] && Math.abs(g.lines.length - 2 * viol - beta) < 1e-9,
    `S1 ${name}: ${pts.length} observables, ${g.lines.length} contexts, the signs violate ${viol}; satisfied minus violated = ${g.lines.length - 2 * viol} = the floor value`);
  results.S1.push({ name, N, observables: pts.length, contexts: g.lines.length, violated: viol, modulus: mu, max_deviation: dev });
  configs[name] = { g, f };
}

/* ------------------------------------------------------------------ S2: every context, ideal sequential measurement */
for (const [name, reps, sample] of [['pivot', 3, 0], ['cieslinski5', 1, 0], ['phase5', 1, 0], ['phase7', 1, FULL7 ? 0 : 30000]]) {
  const { g } = configs[name], N = g.N;
  for (let rep = 0; rep < reps; rep++) {
    const p = randomState(N, rnd);
    const order = sample ? Array.from({ length: sample }, () => rnd.below(g.lines.length)) : rnd.shuffle(g.lines.map((_, i) => i));
    let ok = 0; gateCount = 0; measCount = 0;
    for (const i of order) {
      const [u, v, w, s] = g.lines[i];
      const o = [u, v, w].map((x) => measurePauli(p, N, g.A(x), g.C(x), rnd.unit()));
      if (o[0] * o[1] * o[2] === s) ok++;
    }
    freeState(p);
    check(ok === order.length, `S2 ${name} run ${rep}: ${ok}/${order.length} ${sample ? 'sampled ' : ''}contexts${sample ? ` (of ${g.lines.length})` : ''} give the quantum sign on a random state (${measCount} projective measurements, ${gateCount} gates)`);
    results.S2.push({ name, rep, contexts: g.lines.length, measured: order.length, agree: ok, measurements: measCount, gates: gateCount });
  }
}

/* ------------------------------------------------------------------ S3: noise against the classical ceilings */
for (const [name, degree] of [['pivot', 75], ['cieslinski5', 480], ['phase5', 480], ['phase7', 729344]]) {
  const { g, f } = configs[name], N = g.N, shots = 4000, ceiling = 1 - degree / g.lines.length;
  for (const perr of [0, 0.002, 0.005, 0.01, 0.02, 0.05, 0.1]) {
    const p = randomState(N, rnd);
    let ok = 0, okClassical = 0;
    for (let sh = 0; sh < shots; sh++) {
      const [u, v, w, s] = g.lines[rnd.below(g.lines.length)];
      let prod = 1;
      for (const x of [u, v, w]) { pauliNoise(p, N, rnd, perr); prod *= measurePauli(p, N, g.A(x), g.C(x), rnd.unit()); }
      if (prod === s) ok++;
      if (f[u] * f[v] * f[w] === s) okClassical++;
    }
    freeState(p);
    const fiveSigma = 5 * Math.sqrt(ceiling * (1 - ceiling) / shots);
    const row = { name, noise_per_qubit_per_measurement: perr, shots, quantum_success: ok / shots, optimal_classical_on_same_contexts: okClassical / shots,
      classical_ceiling: ceiling, exceeds_ceiling_by_5_sigma: ok / shots - fiveSigma > ceiling };
    results.S3.push(row);
    log(`S3 ${name} noise=${perr}: simulated success ${(ok / shots).toFixed(4)} | classical ceiling ${ceiling.toFixed(4)} (exact) | optimal classical assignment on the same sample ${(okClassical / shots).toFixed(4)} | above ceiling by 5 sigma: ${row.exceeds_ceiling_by_5_sigma}`);
    if (perr === 0) check(ok === shots, `S3 ${name}: without noise every sampled context gives the quantum sign`);
  }
}
results.random_bytes_used = rnd.used;
results.failures = failures;
writeFileSync(path.join(root, 'results', 'moonlab_saturated.json'), JSON.stringify(results, null, 1));
log(failures === 0 ? 'MOONLAB-SATURATED-PASS' : `MOONLAB-SATURATED-FAIL (${failures})`);
process.exit(failures === 0 ? 0 : 1);
