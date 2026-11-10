/* Compare independently built browser matrices with the exact Python artifact. */
const assert=require('node:assert/strict');
const fs=require('node:fs');
const path=require('node:path');
const c=require('../c3-lab/model.js');
const record=JSON.parse(fs.readFileSync(path.join(__dirname,'../results/frontier-c3-n4-verification.json'),'utf8'));
const result=c.compare(...c.witnesses);
assert.equal(result.status,'certificate passes');
assert.equal(c.section.length,71);assert.equal(c.outside.length,64);
for(let i=0;i<2;i++){
  const r=i===0?result.a:result.b;
  assert.deepEqual(r.characteristic_polynomial,record.runs[i].carrier_charpoly.map(String));
  assert.equal(r.completion_cubic_trace,String(record.runs[i].completion_trace_cube));
  assert.equal(r.outside_contexts,1120);
  assert.deepEqual(r.negative_section_labels,record.runs[i].negative_section_labels);
}
const altered=c.compare(c.witnesses[0],c.witnesses[1].concat(c.pivot));
assert.equal(altered.same_carrier_polynomial,false);
assert.notEqual(altered.status,'certificate passes');
const duplicate=c.compare(c.witnesses[0],c.witnesses[0]);
assert.equal(duplicate.same_carrier_polynomial,true);
assert.equal(duplicate.different_completion_trace,false);
assert.notEqual(duplicate.status,'certificate passes');
assert.throws(()=>c.build([8]),/Invalid sign/);
assert.throws(()=>c.build([128,128]),/Invalid sign/);
console.log('PASS: exact browser/Python agreement; perturbation, identical-pair, and invalid-input controls.');
