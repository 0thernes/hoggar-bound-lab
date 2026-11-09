"""Export independently generated contexts and checked witnesses for the explorer."""
import importlib.util
import json
from pathlib import Path
import numpy as np

ROOT = Path(__file__).resolve().parents[1]
spec = importlib.util.spec_from_file_location('checker',ROOT/'tests/independent_validation.py')
checker = importlib.util.module_from_spec(spec)
spec.loader.exec_module(checker)

profiles = []
for n,kind,name,witness in [
    (3,'f','Three qubits · Hoggar hexagon','n3_f_hoggar_moonlab.txt'),
    (4,'h','Four real qubits · realified Hoggar','n4_h_hoggar_moonlab.txt'),
    (4,'f','Four qubits · a certified gap','n4_f.txt'),
    (5,'h','Five real qubits · beyond one fifth','n5_h.txt'),
    (5,'f','Five qubits · 86,955 constraints','n5_f.txt'),
]:
    points,lines = checker.geometry(n,kind)
    wn,wk,claimed,signs = checker.load_witness(ROOT/'data/witness'/witness)
    assert (wn,wk)==(n,kind) and checker.degree(lines,signs)==claimed
    lower = checker.exact_bound(len(points),len(lines),2**n)
    labels = {v:''.join('IXZY'[c] for c in reversed(checker.codes(n,v))) for v in points}
    profiles.append({'id':str(n)+kind,'name':name,'qubits':n,'family':kind,
        'points':points,'labels':labels,'lines':lines,'negative':np.flatnonzero(signs<0).tolist(),
        'witnessViolations':claimed,'lowerBound':lower,'witnessFile':witness,
        'exact':claimed==lower,
        'theorem': { '3f':'three_qubit_contexts', '4h':'four_qubit_hyperbolic_contexts',
          '4f':'four_qubit_contexts','5h':'five_qubit_hyperbolic_contexts','5f':'five_qubit_contexts'}[str(n)+kind]})
dest=ROOT/'independent-review'
dest.mkdir(exist_ok=True)
(dest/'data.js').write_text('globalThis.HOGGAR_DATA = '+json.dumps(profiles,separators=(',',':'))+';\n',encoding='utf-8')
print(f'Exported {len(profiles)} independently checked profiles')
