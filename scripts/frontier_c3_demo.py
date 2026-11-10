"""Run the exact C3 similarity and completion-moment certificate in Eshkol.

This is a working demonstration of the Tsotchke compiler's exact integer
arithmetic, separate from the Lean proof and independent NumPy verifier.
"""
from pathlib import Path
import hashlib
import json
import os
import shutil
import subprocess
from frontier_c3_integer_bounds import integer_bounds

if not __debug__:
    raise RuntimeError('Verification requires assertions: run Python without -O')

ROOT=Path(__file__).resolve().parents[1]

PROGRAM=r'''
(define (at a n i j) (vector-ref a (+ (* n i) j)))
(define (multiply a b n)
  (let ((out (make-vector (* n n) 0)))
    (let loop-i ((i 0))
      (if (= i n) out
        (begin
          (let loop-j ((j 0))
            (if (= j n) 0
              (begin
                (vector-set! out (+ (* n i) j)
                  (let loop-k ((k 0) (acc 0))
                    (if (= k n) acc
                      (loop-k (+ k 1) (+ acc (* (at a n i k) (at b n k j)))))))
                (loop-j (+ j 1)))))
          (loop-i (+ i 1)))))))
(define (same a b n)
  (let loop ((i 0))
    (if (= i (* n n)) #t
      (and (= (vector-ref a i) (vector-ref b i)) (loop (+ i 1))))))
(define (scaled-identity? a n k)
  (let loop ((i 0))
    (if (= i (* n n)) #t
      (and (= (vector-ref a i) (if (= (quotient i n) (remainder i n)) k 0))
           (loop (+ i 1))))))
(define (trace a n)
  (let loop ((i 0) (acc 0))
    (if (= i n) acc (loop (+ i 1) (+ acc (at a n i i))))))
(define (block a start)
  (let ((out (make-vector 64 0)))
    (let loop ((i 0))
      (if (= i 64) out
        (begin (vector-set! out i (at a 16 (+ start (quotient i 8)) (+ start (remainder i 8))))
               (loop (+ i 1)))))))
(define (completion-cube a)
  (let* ((p (block a 0)) (m (block a 8))
         (p2 (multiply p p 8)) (m2 (multiply m m 8))
         (p3 (multiply p p2 8)) (m3 (multiply m m2 8)))
    (quotient (+ (* 8 (+ (trace p3 8) (trace m3 8)))
                 (* 3 (+ (* (trace p2 8) (trace m 8)) (* (trace p 8) (trace m2 8))))) 8)))
(define intertwines (same (multiply A M 16) (multiply M B 16) 16))
(define right-inverse (scaled-identity? (multiply M R 16) 16 46656))
(define left-inverse (scaled-identity? (multiply R M 16) 16 46656))
(define cube-a (completion-cube A))
(define cube-b (completion-cube B))
(define ok (and intertwines right-inverse left-inverse (= cube-a 14976) (= cube-b 15360)))
(display "{\"intertwines\":") (display (if intertwines "true" "false"))
(display ",\"right_inverse\":") (display (if right-inverse "true" "false"))
(display ",\"left_inverse\":") (display (if left-inverse "true" "false"))
(display ",\"completion_cube_a\":") (display cube-a)
(display ",\"completion_cube_b\":") (display cube-b)
(display ",\"pass\":") (display (if ok "true" "false")) (display "}") (newline)
'''

def main():
    certificate=ROOT/'results/frontier-c3-n4-similarity.json'
    data=json.loads(certificate.read_text())
    bound_report=integer_bounds(data)
    declarations=[]
    for key in ['A','B','M','R']:
        declarations.append('(define '+key+' (vector '+' '.join(str(v) for row in data[key] for v in row)+'))\n')
    program=''.join(declarations)+PROGRAM
    target=ROOT/'build/frontier_c3_demo.esk'
    target.parent.mkdir(exist_ok=True)
    target.write_text(program)
    eshkol=os.environ.get('ESHKOL_RUN') or shutil.which('eshkol-run')
    if not eshkol and os.name=='nt':eshkol=r'Z:\Tools\eshkol\current\bin\eshkol-run.exe'
    if not eshkol or not Path(eshkol).is_file():raise RuntimeError('Set ESHKOL_RUN to the Eshkol executable')
    # Use an existing matching installation only in this child process. Do not
    # edit the installed compiler, user environment, registry, or global PATH.
    env=os.environ.copy();overrides={};path_prepend=[]
    llvm=Path('Z:/Tools/LLVM-21')
    cuda=Path('Z:/Tools/cuda-12.9-redist')
    if os.name=='nt':
        compiler=llvm/'bin/clang++.exe'
        builtins=llvm/'lib/clang/21/lib/windows/clang_rt.builtins-x86_64.lib'
        if compiler.is_file() and builtins.is_file():
            for name,value in [('ESHKOL_CXX_COMPILER',str(compiler)),('LLVM_HOME',str(llvm))]:
                if not env.get(name):overrides[name]=value
        if (cuda/'lib/x64/cudart.lib').is_file() and (cuda/'bin/cudart64_12.dll').is_file():
            for name,value in [('ESHKOL_CUDA_LIBRARY_PATH',str(cuda/'lib/x64')),('CUDA_HOME',str(cuda))]:
                if not env.get(name):overrides[name]=value
            path_prepend.append(str(cuda/'bin'))
    env.update(overrides)
    if path_prepend:env['PATH']=os.pathsep.join(path_prepend+[env.get('PATH','')])
    version=subprocess.check_output([eshkol,'--version'],env=env,text=True).strip()
    command=[eshkol,'-r',str(target)]
    result=subprocess.run(command,cwd=ROOT,env=env,text=True,capture_output=True)
    log='returncode: '+str(result.returncode)+'\n--- stdout ---\n'+result.stdout+'--- stderr ---\n'+result.stderr
    (ROOT/'results/frontier-c3-eshkol.log').write_text(log,encoding='utf8')
    parsed=None
    try:
        records=[json.loads(line) for line in result.stdout.splitlines() if line.startswith('{')]
        if len(records)==1:parsed=records[0]
    except json.JSONDecodeError:
        pass
    expected={'intertwines':True,'right_inverse':True,'left_inverse':True,
              'completion_cube_a':14976,'completion_cube_b':15360,'pass':True}
    passed=result.returncode==0 and parsed==expected
    report={'status':'pass' if passed else 'fail','eshkol_version':version,'checks':parsed,
            'integer_bound':bound_report['maximum_absolute_intermediate'],
            'integer_bound_below_signed_64_bit':True,
            'certificate_sha256':hashlib.sha256(certificate.read_bytes()).hexdigest(),
            'eshkol_program_sha256':hashlib.sha256(program.encode()).hexdigest(),
            'runner_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
            'execution':{'command':command,'cwd':str(ROOT),'returncode':result.returncode,
                         'stdout':result.stdout,'stderr':result.stderr,
                         'stderr_empty':not result.stderr,
                         'process_local_environment_overrides':overrides,
                         'process_local_path_prepend':path_prepend,
                         'scope':'Serial integer certificate through eshkol-run -r. This CLI may link and run a temporary native executable; no GPU or parallel-worker APIs are invoked. This does not qualify CUDA, parallel workers, or all compiler modes.'},
            'meaning':'Exact integer identities certify rational carrier similarity and unequal completion cubic traces'}
    (ROOT/'results/frontier-c3-eshkol.json').write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps(report,indent=2))
    if not passed:raise RuntimeError('Eshkol certificate failed; see recorded stdout, stderr and returncode')

if __name__=='__main__':main()
