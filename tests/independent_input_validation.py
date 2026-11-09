"""Regression tests for bounded witness parsing and CLI geometry validation.

Run after building: python tests/independent_input_validation.py
Optional arguments: <hoggar-binary> <qgt-binary>.
Every malformed input must exit 2; crashes and accidental success fail.
"""
import hashlib
import json
from pathlib import Path
import subprocess
import sys
import tempfile

ROOT = Path(__file__).resolve().parents[1]
HOGGAR = ROOT / (sys.argv[1] if len(sys.argv)>1 else 'build/hoggar-independent.exe')
QGT = ROOT / (sys.argv[2] if len(sys.argv)>2 else 'build/qgt-independent.exe')
results = []


def check(label, args, code=0, contains=None):
    p = subprocess.run([str(x) for x in args], cwd=ROOT, text=True,
                       capture_output=True, timeout=30)
    if p.returncode != code or (contains is not None and contains not in p.stdout):
        raise AssertionError((label, p.returncode, p.stdout, p.stderr))
    results.append({'case':label, 'exit_code':p.returncode})


source = (ROOT/'data/witness/n3_f_hoggar_moonlab.txt').read_text().split()
header = ' '.join(source[:3])
hexword = source[3]
good = header+'\n'+hexword+'\n'

# Both consumers must accept the genuine certificates after the parser change.
for path in sorted((ROOT/'data/witness').glob('*.txt')):
    n, typ, count = path.read_text().split()[:3]
    check('trusted '+path.name, [HOGGAR, 'verify', n, typ, path], contains='violated='+count+' ')
check('trusted QGTL pair', [QGT], contains='|F| = 0 max deviation')

bad = {
    'empty': '',
    'missing hex': header+'\n',
    'wrong N': '4 f 63\n'+hexword,
    'negative N': '-3 f 63\n'+hexword,
    'overflow N': '18446744073709551616 f 63\n'+hexword,
    'unknown type': '3 z 63\n'+hexword,
    'long type': '3 full 63\n'+hexword,
    'quadric expansion': '3 h 63\n'+hexword,
    'negative count': '3 f -1\n'+hexword,
    'overflow count': '3 f 18446744073709551616\n'+hexword,
    'impossible count': '3 f 316\n'+hexword,
    'count suffix': '3 f 63oops\n'+hexword,
    'NUL header': '3\x00oops f 63\n'+hexword,
    'invalid hex': header+'\n'+'g'+hexword[1:],
    'punctuation hex': header+'\n'+'!'+hexword[1:],
    'NUL hex': header+'\n'+'\x00'+hexword[1:],
    'short hex': header+'\n'+hexword[:-1],
    'long hex': header+'\n'+hexword+'0',
    'megabyte hex': header+'\n'+'a'*(1<<20),
    'internal whitespace': header+'\n'+hexword[:8]+' '+hexword[8:],
    'trailing token': good+'unexpected',
    'trailing second hex': good+hexword,
}
with tempfile.TemporaryDirectory(prefix='witness-input-', dir=ROOT/'build') as tmp:
    file = Path(tmp)/'test.txt'
    for label, content in bad.items():
        file.write_bytes(content.encode())
        check('hoggar '+label, [HOGGAR, 'verify', '3', 'f', file], 2)
        check('qgt '+label, [QGT, file], 2)
    for label, content in {'uppercase':header+'\n'+hexword.upper()+'\n',
                           'whitespace':good+' \r\n\t'}.items():
        file.write_bytes(content.encode())
        check('hoggar '+label, [HOGGAR, 'verify', '3', 'f', file])
        check('qgt '+label, [QGT, file])
    file.write_text(good)
    for typ in ('h', 'e'):
        check('full-space restriction '+typ, [HOGGAR, 'verify', '3', typ, file])
        check('full-space search seed '+typ,
              [HOGGAR, 'search', '3', typ, '1', '1', '0', '0.8', '0.05', file, '-'])
    file.write_text('3 h 63\n'+hexword+'\n')
    check('incompatible quadric', [HOGGAR, 'verify', '3', 'e', file], 2)

for n in ('-1', '0', '1', '8', '16', '999999999999999999999', 'x', '4oops'):
    check('invalid N '+n, [HOGGAR, 'lines', n, 'f'], 2)
for typ in ('', 'full', 'z'):
    check('invalid type '+repr(typ), [HOGGAR, 'lines', '2', typ], 2)
for n in ('-1','8','garbage'):
    check('invalid table '+n, [HOGGAR, 'table', n], 2)
check('exhaust extra argument', [HOGGAR, 'exhaust2', 'extra'], 2)
base = ['search','2','f','1','1','0','0.8','0.05','-','-']
for position, token in [(3,'-1'),(3,'18446744073709551616'),(4,'0'),(4,'-1'),
                        (4,'2147483648'),(5,'-1'),(6,'nan'),(6,'inf'),(6,'0'),
                        (7,'-0.5'),(7,'0.2oops')]:
    args = base.copy()
    args[position] = token
    check('invalid search '+str(position)+' '+token, [HOGGAR]+args, 2)
for trial in ('0','-1','1oops'):
    check('invalid trials '+trial, [HOGGAR, 'falsify','2','f','1',trial,'0'], 2)
check('invalid claim', [HOGGAR,'verify','3','f',ROOT/'data/witness/n3_f_hoggar_moonlab.txt','garbage'],2)
check('QGT extra arguments',[QGT,'one','two','three'],2)
check('zero-step search remains valid',[HOGGAR]+base)

report = {'status':'pass','cases':len(results),'results':results,
          'source_sha256':{str(p.relative_to(ROOT)):hashlib.sha256(p.read_bytes()).hexdigest()
                           for p in [ROOT/'src/hoggar.c',ROOT/'src/qgt_hoggar.c',ROOT/'src/witness_io.h']}}
(ROOT/'results/independent-input-validation.json').write_text(json.dumps(report,indent=2)+'\n')
print('PASS: '+str(len(results))+' trusted-witness, malformed-input, and CLI regression cases')
