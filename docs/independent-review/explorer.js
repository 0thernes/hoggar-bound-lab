(() => {
  const $ = id => document.getElementById(id);
  const profiles = globalThis.HOGGAR_DATA;
  let model, positions=[], selected=null, running=false;
  profiles.forEach(p => {const o=document.createElement('option');o.value=p.id;o.textContent=p.name;$('profile').append(o);});
  const fmt=n=>n.toLocaleString('en-US');
  function choose(){running=false;model=new ContextModel(profiles.find(p=>p.id===$('profile').value));selected=null;makeButtons();update();}
  function makeButtons(){
    $('point-buttons').replaceChildren();
    for(const p of model.profile.points){const b=document.createElement('button');b.id='point-'+p;b.addEventListener('click',()=>{model.flip(p);selected=p;update();announce(`Flipped ${model.profile.labels[p]}.`);});$('point-buttons').append(b);}
  }
  function update(){
    const p=model.profile,L=p.lines.length,d=model.violations;
    $('violations').textContent=fmt(d);$('context-count').textContent=`of ${fmt(L)} contexts`;
    $('floor').textContent=fmt(p.lowerBound);$('witness').textContent=fmt(p.witnessViolations);
    $('success').textContent=(100*(1-d/L)).toFixed(1)+'%';
    $('gap').textContent=p.exact?'meets the bound exactly':`${fmt(p.witnessViolations-p.lowerBound)} above our proven floor`;
    $('theorem').textContent='HoggarBound.'+p.theorem;
    $('point-count').textContent=`(${p.points.length})`;
    $('result-title').textContent=d===p.lowerBound?'The bound is saturated.':d<p.lowerBound?'Candidate counterexample.':'The obstruction persists.';
    $('result-copy').textContent=d===p.lowerBound?`This assignment violates exactly ${fmt(d)} contexts. The universal lower bound proves that no assignment can do better.`:d<p.lowerBound?'Export this assignment and check it with the independent verifier. An implementation error must be ruled out before challenging the formal theorem.':`Your assignment violates ${fmt(d)} contexts. Lean proves every assignment must violate at least ${fmt(p.lowerBound)}. `+(p.exact?`The stored witness attains that minimum.`:`The stored witness gives an upper bound of ${fmt(p.witnessViolations)}; a gap remains in this lab’s bound.`);
    p.points.forEach(v=>{const b=$('point-'+v),s=model.signs[v];b.className=s<0?'neg':'pos';b.textContent=p.labels[v]+(s<0?' −':' +');b.setAttribute('aria-label',`Flip ${p.labels[v]}, currently ${s}`);});
    $('context-rows').replaceChildren();
    p.lines.filter((_,i)=>model.bad[i]).slice(0,12).forEach(([u,v,w,s])=>{const tr=document.createElement('tr');[`${p.labels[u]} · ${p.labels[v]} · ${p.labels[w]}`,s>0?'+1':'−1',s>0?'−1':'+1'].forEach(t=>{const td=document.createElement('td');td.textContent=t;tr.append(td);});$('context-rows').append(tr);});
    draw();
  }
  function announce(text){$('action-status').textContent=text;}
  function draw(){
    const c=$('graph'),rect=c.getBoundingClientRect(),dpr=window.devicePixelRatio||1,w=rect.width,h=rect.height;
    c.width=Math.round(w*dpr);c.height=Math.round(h*dpr);const ctx=c.getContext('2d');ctx.scale(dpr,dpr);ctx.clearRect(0,0,w,h);
    const p=model.profile,n=p.points.length,r=Math.min(w,h)*.41;
    positions=p.points.map((v,i)=>{const a=2*Math.PI*i/n-Math.PI/2,ring=n<=63?1:(i%3===0?.63:1);return {v,x:w/2+r*ring*Math.cos(a),y:h/2+r*ring*Math.sin(a)};});
    const map=new Map(positions.map(v=>[v.v,v]));
    let indices=model.bad.map((b,i)=>b?i:-1).filter(i=>i>=0);
    if(selected!==null)indices=indices.filter(i=>p.lines[i].slice(0,3).includes(selected));
    const count=indices.length;indices=indices.slice(0,350);
    ctx.lineWidth=selected===null?.55:1.3;ctx.strokeStyle=selected===null?'rgba(255,141,120,.19)':'rgba(255,141,120,.65)';
    for(const i of indices){const pts=p.lines[i].slice(0,3).map(v=>map.get(v));ctx.beginPath();ctx.moveTo(pts[0].x,pts[0].y);ctx.lineTo(pts[1].x,pts[1].y);ctx.lineTo(pts[2].x,pts[2].y);ctx.closePath();ctx.stroke();}
    for(const q of positions){const active=q.v===selected;ctx.fillStyle=model.signs[q.v]<0?'#ff8d78':'#a7f3cc';ctx.beginPath();ctx.arc(q.x,q.y,active?6:n<=63?4:2.4,0,Math.PI*2);ctx.fill();if(active){ctx.strokeStyle='#eef4ed';ctx.lineWidth=1.5;ctx.stroke();}}
    ctx.fillStyle='#eef4ed';ctx.textAlign='center';ctx.font='500 25px system-ui';ctx.fillText(selected===null?fmt(model.violations):p.labels[selected],w/2,h/2-4);ctx.fillStyle='#a2b4b8';ctx.font='10px system-ui';ctx.fillText(selected===null?'VIOLATED CONTEXTS':'SELECTED OBSERVABLE',w/2,h/2+18);
    $('draw-count').textContent=selected!==null?`${count} violations touch selected point`:`${indices.length} of ${fmt(count)} violations drawn`;
  }
  $('graph').addEventListener('click',e=>{const r=$('graph').getBoundingClientRect(),x=e.clientX-r.left,y=e.clientY-r.top;let nearest=null,dist=100;for(const p of positions){const dd=(p.x-x)**2+(p.y-y)**2;if(dd<dist){dist=dd;nearest=p;}}if(nearest){selected=nearest.v;model.flip(selected);announce(`Flipped ${model.profile.labels[selected]}. Click empty space to show all contexts.`);}else selected=null;update();});
  $('profile').addEventListener('change',()=>{choose();announce('Loaded an independently checked witness.');});
  $('reset').addEventListener('click',()=>{running=false;model.reset();selected=null;update();announce('Stored witness restored.');});
  $('random').addEventListener('click',()=>{running=false;model.randomize();selected=null;update();announce('Random assignment generated in this browser. This is not a quantum random source.');});
  $('greedy').addEventListener('click',()=>{if(running)return;running=true;selected=null;let steps=0;function step(){if(!running)return;const changed=model.bestFlip();steps++;update();if(changed!==null&&steps<80)requestAnimationFrame(step);else{running=false;announce(changed===null?`Reached a single-flip local minimum after ${steps-1} improvements. This does not prove global optimality.`:'Stopped after 80 improvements; click Improve signs to continue.');}}requestAnimationFrame(step);});
  $('export').addEventListener('click',()=>{const blob=new Blob([model.serialize()],{type:'text/plain'}),a=document.createElement('a'),url=URL.createObjectURL(blob);a.href=url;a.download=`hoggar-${model.profile.id}-${model.violations}.txt`;a.click();setTimeout(()=>URL.revokeObjectURL(url),1000);announce('Exported assignment in the C verifier’s witness format.');});
  window.addEventListener('resize',draw);choose();
})();
