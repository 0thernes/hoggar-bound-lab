"""Publication figures: deterministic analytic curves and certified finite intervals."""
from pathlib import Path
import numpy as np
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt

ROOT=Path(__file__).resolve().parents[1]
out=ROOT/'paper'/'independent-figures'
out.mkdir(parents=True,exist_ok=True)
plt.rcParams.update({'font.family':'DejaVu Sans','font.size':10,'axes.spines.top':False,
                     'axes.spines.right':False,'svg.fonttype':'none','pdf.fonttype':42})
fig,(ax,bx)=plt.subplots(1,2,figsize=(11.8,4.8),layout='constrained')
ns=np.arange(2,13)
D=2.**ns
bound=.5-np.sqrt(D+1)/(D+2)
ax.plot(ns,bound,'o-',color='#116755',lw=2,label='Spectral lower bound')
ax.axhline(.5,color='#353a42',ls=':',label='Random-assignment existence bound')
ax.axhline(.2,color='#ae603b',ls='--',label='Published one-fifth baseline')
ax.fill_between(ns,bound,.5,color='#116755',alpha=.08)
ax.set(xlabel='Qubits N (dimension D = 2ᴺ)',ylabel='Minimum violated fraction d / L',
       title='A. Full Pauli-line family',ylim=(0,.54),xticks=ns[::2])
ax.legend(fontsize=8,loc='lower right',frameon=False)
ax.grid(axis='y',alpha=.17)
cases=[('Full 3',63,315,63),('Real 4',315,1575,315),('Full 4',1451,5355,1575),
       ('Real 5',6426,23715,6975),('Full 5',28786,86955,31479)]
for i,(name,lower,L,upper) in enumerate(cases):
    lo,hi=lower/L,upper/L
    bx.plot([lo,hi],[i,i],color='#8f493a',lw=4,solid_capstyle='round')
    bx.plot(lo,i,'|',color='#116755',ms=15,mew=2)
    bx.plot(hi,i,'o',color='#8f493a',ms=5)
    bx.annotate(f'{lower:,} ≤ d ≤ {upper:,}',(hi,i),xytext=(8,-4),textcoords='offset points',fontsize=8)
bx.set(yticks=range(5),yticklabels=[c[0] for c in cases],xlabel='Minimum violated fraction d / L',
       title='B. Bounds established by this artifact',xlim=(.17,.47),ylim=(-.6,4.6))
bx.invert_yaxis();bx.grid(axis='x',alpha=.17)
bx.text(.01,-.21,'Intervals are mathematical bounds, not confidence intervals.\nStronger external claims are discussed in the literature audit.',transform=bx.transAxes,fontsize=8,color='#555')
for suffix in ('pdf','svg','png'):
    fig.savefig(out/f'spectral-bounds.{suffix}',dpi=220,bbox_inches='tight')
print(out/'spectral-bounds.pdf')
