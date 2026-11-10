/* Integer Pauli construction and exact certificates. No dependencies. */
(function (root) {
  'use strict';
  const N = 4, D = 16, pivot = 128;
  const pop = x => { let n = 0; for (; x; x &= x - 1) n++; return n; };
  const real = v => pop((v & 15) & (v >> 4)) % 2 === 0;
  const commute = (u, v) => (pop((u & 15) & (v >> 4)) + pop((v & 15) & (u >> 4))) % 2 === 0;
  const points = Array.from({length: 255}, (_, i) => i + 1).filter(real);
  const section = points.filter(v => commute(v, pivot));
  const outside = points.filter(v => !commute(v, pivot));
  const zero = n => Array.from({length:n}, () => Array(n).fill(0));
  function pauli(v) {
    const a = v & 15, c = v >> 4, phase = pop(a & c) / 2;
    if (!Number.isInteger(phase)) throw Error('Only real Paulis are supported');
    const p = zero(D);
    for (let j = 0; j < D; j++) p[j ^ a][j] = (pop(c & j) + phase) % 2 ? -1 : 1;
    return p;
  }
  const matrices = Object.fromEntries(points.map(v => [v, pauli(v)]));
  const witnesses = [[48,102,176,230], [87,144,176,215]];
  const coefficients = ['1','0','-568','-6112','4716','302272','1056216','-1584288',
    '-15112746','-24586112','22670136','142620896','242617100','224392896',
    '121805992','36642720','4741425'];
  function label(v) {
    let s = '';
    for (let j = N - 1; j >= 0; j--) s += ['I','X','Z','Y'][((v >> j) & 1) + 2 * ((v >> (N + j)) & 1)];
    return s;
  }
  function build(negative) {
    const neg = new Set(negative);
    if (negative.length !== neg.size || negative.some(v => !section.includes(v))) throw Error('Invalid sign assignment');
    const sign = v => neg.has(v) ? -1 : 1;
    const carrier = zero(D), completion = zero(outside.length);
    for (const v of section) for (let i=0;i<D;i++) for (let j=0;j<D;j++) carrier[i][j] += sign(v)*matrices[v][i][j];
    let contexts = 0;
    for (let i=0;i<outside.length;i++) for (let j=i+1;j<outside.length;j++) {
      const u=outside[i], v=outside[j], s=u^v;
      if (!commute(u,v)) continue;
      if (!section.includes(s)) throw Error('Outside pair has no section point');
      const a=u&15,b=v&15;
      const product=matrices[u][a^b][b]*matrices[v][b][0]*matrices[s][a^b][0];
      if (Math.abs(product)!==1) throw Error('Invalid context sign');
      completion[i][j]=completion[j][i]=product*sign(s);
      contexts++;
    }
    return {carrier,completion,contexts};
  }
  function characteristic(matrix) {
    const n=matrix.length, a=matrix.map(row=>row.map(BigInt));
    let b=Array.from({length:n},(_,i)=>Array.from({length:n},(_,j)=>i===j?1n:0n));
    const coeff=[1n];
    for (let k=1;k<=n;k++) {
      const c=Array.from({length:n},()=>Array(n).fill(0n));
      for(let i=0;i<n;i++) for(let t=0;t<n;t++) if(a[i][t]!==0n)
        for(let j=0;j<n;j++) c[i][j]+=a[i][t]*b[t][j];
      const trace=c.reduce((s,row,i)=>s+row[i],0n);
      if(trace%BigInt(k)!==0n) throw Error('Nonintegral characteristic coefficient');
      const ck=-trace/BigInt(k); coeff.push(ck);
      for(let i=0;i<n;i++) c[i][i]+=ck;
      b=c;
    }
    return coeff.map(String);
  }
  function traceCube(a) {
    let value=0n;
    for(let i=0;i<a.length;i++) for(let j=0;j<a.length;j++) if(a[i][j])
      for(let k=0;k<a.length;k++) if(a[j][k] && a[k][i]) value+=BigInt(a[i][j])*BigInt(a[j][k])*BigInt(a[k][i]);
    return String(value);
  }
  function verify(negative) {
    const m=build(negative);
    return {negative_section_labels:negative.slice().sort((a,b)=>a-b),
      characteristic_polynomial:characteristic(m.carrier),
      completion_cubic_trace:traceCube(m.completion),outside_contexts:m.contexts,
      section_points:section.length,outside_points:outside.length};
  }
  function compare(first,second) {
    const a=verify(first),b=verify(second);
    return {status:JSON.stringify(a.characteristic_polynomial)===JSON.stringify(b.characteristic_polynomial)
      && a.completion_cubic_trace!==b.completion_cubic_trace?'certificate passes':'not this certificate',
      same_carrier_polynomial:JSON.stringify(a.characteristic_polynomial)===JSON.stringify(b.characteristic_polynomial),
      different_completion_trace:a.completion_cubic_trace!==b.completion_cubic_trace,
      arithmetic:'JavaScript BigInt; characteristic polynomial via exact Faddeev-LeVerrier recurrence',a,b};
  }
  const api={N,D,pivot,section,outside,witnesses,coefficients,label,build,characteristic,traceCube,verify,compare};
  if(typeof module!=='undefined' && module.exports) module.exports=api;
  else root.C3=api;
})(typeof globalThis==='undefined'?this:globalThis);
