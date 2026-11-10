"""Plot the exact C3 witness's spectra; floating point is used only for display."""
from pathlib import Path
import json
import numpy as np
import matplotlib
matplotlib.use('Agg')
import matplotlib.pyplot as plt

ROOT=Path(__file__).resolve().parents[1]

def main():
    data=json.loads((ROOT/'results/frontier-c3-n4-pair.json').read_text())['pair']
    spectra=[]
    for row in data:
        plus=np.linalg.eigvalsh(np.array(row['plus'],dtype=float))
        minus=np.linalg.eigvalsh(np.array(row['minus'],dtype=float))
        spectra.append((np.sort(np.r_[plus,minus]),np.sort(((plus[:,None]+minus[None,:])/2).ravel())))
    plt.rcParams.update({'font.family':'DejaVu Sans','font.size':9,'axes.spines.top':False,'axes.spines.right':False,
                         'axes.titleweight':'bold','pdf.fonttype':42,'svg.fonttype':'none'})
    fig,axs=plt.subplots(1,2,figsize=(9,3.4),gridspec_kw={'width_ratios':[1,1.45]})
    colors=['#167367','#b45d12']
    for k,(carrier,completion) in enumerate(spectra):
        axs[0].plot(np.arange(1,17),carrier,marker='o' if k==0 else 'x',ms=5,
                    linewidth=1 if k==0 else 0,alpha=.85,color=colors[k],label='Assignment '+('A' if k==0 else 'B'))
        axs[1].plot(np.arange(1,65),completion,marker='.' if k==0 else 'x',ms=3.6,linewidth=.9,
                    alpha=.9,color=colors[k],label='Assignment '+('A' if k==0 else 'B'))
    axs[0].set(title='Identical carrier spectra',xlabel='Ordered eigenvalue index',ylabel='Eigenvalue')
    axs[1].set(title='Different completion spectra',xlabel='Ordered eigenvalue index',ylabel='Eigenvalue')
    for ax in axs:
        ax.axhline(0,color='#c7d0d2',linewidth=.7,zorder=0)
        ax.grid(axis='y',alpha=.15);ax.legend(frameon=False,fontsize=8,loc='upper left')
    axs[1].text(.98,.08,'Exact cubic traces: 14,976 and 15,360\nExact largest-eigenvalue gap: 2',
                ha='right',transform=axs[1].transAxes,fontsize=8,color='#31434a')
    fig.tight_layout(pad=1.3)
    dest=ROOT/'paper/c3-figures';dest.mkdir(exist_ok=True)
    for extension in ['png','pdf','svg']:
        fig.savefig(dest/('spectra.'+extension),dpi=200,bbox_inches='tight')
    print(json.dumps({'carrier_max_abs_display_difference':float(np.max(abs(spectra[0][0]-spectra[1][0]))),
                      'completion_maxima':[float(s[1][-1]) for s in spectra],
                      'purpose':'Numerical illustration only; exact proof is in integer and Lean certificates'},indent=2))

if __name__=='__main__':main()
