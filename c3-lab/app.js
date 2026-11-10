'use strict';
const byId=id=>document.getElementById(id);
let first=C3.witnesses[0].slice(),second=C3.witnesses[1].slice(),last=null;
function renderSigns(){
  for(const [id,values] of [['signs-a',first],['signs-b',second]]){
    byId(id).replaceChildren(...values.slice().sort((a,b)=>a-b).map(v=>{const e=document.createElement('code');e.textContent='−'+C3.label(v);return e;}));
  }
  byId('count-b').textContent=second.length+' negative signs';
  byId('all-signs').replaceChildren(...C3.section.map(v=>{
    const b=document.createElement('button');b.textContent=(second.includes(v)?'−':'+')+C3.label(v);
    b.className=second.includes(v)?'negative':'';b.setAttribute('aria-pressed',String(second.includes(v)));
    b.onclick=()=>{second=second.includes(v)?second.filter(x=>x!==v):second.concat(v);invalidate();};return b;
  }));
}
function invalidate(){
  last=null;renderSigns();byId('status').className='';byId('status').textContent='Assignment changed. Run exact verification to check it.';
  for(const id of ['trace-a','trace-b'])byId(id).textContent='—';
  for(const id of ['carrier-check','completion-check'])byId(id).textContent='Not checked';
  byId('polynomial').textContent='Run verification to compute.';
  byId('factor').hidden=true;byId('download').disabled=true;
}
async function run(){
  byId('run').disabled=true;byId('status').className='';byId('status').textContent='Building both carriers and both completion matrices; checking exact integers…';
  await new Promise(resolve=>setTimeout(resolve,30));
  try{
    last=C3.compare(first,second);
    byId('trace-a').textContent=Number(last.a.completion_cubic_trace).toLocaleString();
    byId('trace-b').textContent=Number(last.b.completion_cubic_trace).toLocaleString();
    byId('carrier-check').textContent=last.same_carrier_polynomial?'Exactly equal':'Different';
    byId('completion-check').textContent=last.different_completion_trace?'Different — spectra cannot match':'Equal — this check is inconclusive';
    byId('status').className=last.status==='certificate passes'?'pass':'fail';
    byId('status').textContent=last.status==='certificate passes'?'PASS · Exact carrier cospectrality, different completion spectra.':'This assignment does not pass the counterexample certificate.';
    byId('polynomial').textContent='A: '+last.a.characteristic_polynomial.join(', ')+'\nB: '+last.b.characteristic_polynomial.join(', ');
    byId('factor').hidden=!(last.same_carrier_polynomial&&JSON.stringify(last.a.characteristic_polynomial)===JSON.stringify(C3.coefficients));
    byId('download').disabled=false;
  }catch(e){byId('status').className='fail';byId('status').textContent='Verification failed: '+e.message;}
  finally{byId('run').disabled=false;}
}
byId('run').onclick=run;
byId('perturb').onclick=()=>{second=second.includes(C3.pivot)?second.filter(v=>v!==C3.pivot):second.concat(C3.pivot);invalidate();};
byId('restore').onclick=()=>{first=C3.witnesses[0].slice();second=C3.witnesses[1].slice();invalidate();run();};
byId('download').onclick=()=>{if(!last)return;const u=URL.createObjectURL(new Blob([JSON.stringify(last,null,2)+'\n'],{type:'application/json'}));const a=document.createElement('a');a.href=u;a.download='c3-exact-browser-certificate.json';a.click();setTimeout(()=>URL.revokeObjectURL(u),1000);};
renderSigns();byId('download').disabled=true;run();
