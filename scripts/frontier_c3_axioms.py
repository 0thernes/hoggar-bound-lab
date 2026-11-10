"""Require every declaration requested by the C3 audit to use only standard Lean axioms."""
from pathlib import Path
import argparse
import json
import re

ROOT=Path(__file__).resolve().parents[1]

def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('log',type=Path)
    parser.add_argument('--source',type=Path,default=ROOT/'lean/C3Verification.lean')
    parser.add_argument('--minimum',type=int,default=10)
    parser.add_argument('--output',type=Path,default=ROOT/'results/frontier-c3-axioms.json')
    args=parser.parse_args()
    source=args.source.read_text(encoding='utf-8')
    expected=set(re.findall(r'#print axioms\s+(\S+)',source))
    if len(expected)<max(1,args.minimum):raise RuntimeError('The audited declaration list is unexpectedly short')
    log=args.log.read_text(encoding='utf-8')
    found={name:{a.strip() for a in axioms.split(',') if a.strip()}
           for name,axioms in re.findall(r"'([^']+)' depends on axioms:\s*\[([^\]]*)\]",log)}
    for name in re.findall(r"'([^']+)' does not depend on any axioms",log):found[name]=set()
    if not expected<=found.keys():raise RuntimeError('Missing declaration reports: '+str(sorted(expected-found.keys())))
    allowed={'propext','Classical.choice','Quot.sound'}
    for name in expected:
        if not found[name]<=allowed:raise RuntimeError('Unapproved axioms in '+name+': '+str(found[name]-allowed))
    report={'status':'pass','declarations':len(expected),'allowed_axioms':sorted(allowed),
            'actual':{name:sorted(found[name]) for name in sorted(expected)}}
    args.output.write_text(json.dumps(report,indent=2)+'\n',encoding='utf-8')
    print(f'PASS: {len(expected)} audited declarations use only standard Lean axioms.')

if __name__=='__main__':main()
