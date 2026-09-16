"""Fresh-process regression for arbitrary-size permitted witness coordinates."""
import json
import subprocess
import sys
from pathlib import Path

sys.set_int_max_str_digits(0)
HERE=Path(__file__).resolve().parent
ALGORITHM=HERE.parents[1]/'work/algorithm.py'
payload=json.loads((HERE/'large-valid-witness.json').read_text())

def check(name,payload):
    p=subprocess.run([sys.executable,str(ALGORITHM),'--extract'],input=json.dumps(payload),capture_output=True,text=True)
    assert p.returncode==0,p.stderr
    assignment=json.loads(p.stdout)
    assert all(any(assignment[abs(l)-1]==(l>0) for l in clause) for clause in payload['source']['clauses'])
    print(json.dumps({'case':name,'assignment':assignment,'passed':True}))

check('saved_large_rational_witness',payload)
# The unique root of x-c is precisely c, including for c=0.
# Replacing integer rational W coordinates by these dense polynomial encodings
# leaves every factor value and hence the already validated target product intact.
payload['target_solution']['W']=[[{'poly':[-int(c),1],'root':1} for c in row] for row in payload['target_solution']['W']]
check('large_json_integer_polynomial_coefficients',payload)
