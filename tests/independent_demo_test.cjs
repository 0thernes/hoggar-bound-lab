const assert = require('node:assert/strict');
require('../independent-review/data.js');
const {ContextModel} = require('../independent-review/model.js');
let seed = 20261109;
const random = () => ((seed=(Math.imul(seed,1664525)+1013904223)>>>0)/4294967296);
let flips = 0;
for (const profile of globalThis.HOGGAR_DATA) {
  const m = new ContextModel(profile);
  assert.equal(m.violations, profile.witnessViolations);
  for (let k=0;k<150;k++) {
    m.flip(profile.points[Math.floor(random()*profile.points.length)]);
    const slow = profile.lines.reduce((n,[u,v,w,s])=>n+(m.signs[u]*m.signs[v]*m.signs[w]!==s),0);
    assert.equal(m.violations,slow);
    assert(m.violations >= profile.lowerBound);
    flips++;
  }
  m.randomize(random);
  for(let k=0;k<30;k++) {const before=m.violations;m.bestFlip();assert(m.violations<=before);}
  m.reset();
  const [header,hex] = m.serialize().trim().split('\n');
  assert.equal(header,`${profile.qubits} ${profile.family} ${profile.witnessViolations}`);
  const bits=BigInt('0x'+hex);
  profile.points.forEach(p=>assert.equal(((bits>>BigInt(p))&1n)===1n,m.signs[p]<0));
}
console.log(JSON.stringify({status:'passed',profiles:globalThis.HOGGAR_DATA.length,incrementalFlipsCompared:flips,greedyAndExport:true}));
