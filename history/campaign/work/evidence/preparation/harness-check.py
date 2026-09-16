import json
import sys
from pathlib import Path
sys.path.insert(0,str(Path(__file__).resolve().parents[2]))
from check import run_candidate
base=Path(__file__).parent
s={'variables':[0],'clauses':[[1]]}
fixtures={
 'malformed-output':'print("{}")',
 'wrong-decision':'import json; print(json.dumps({"X":[[1,0,0],[0,1,0],[0,0,1]],"tau":0}))',
 'wrong-recovery':'import sys,json; print(json.dumps([False] if "--extract" in sys.argv else {"X":[[0]],"tau":0}))'
}
for name,code in fixtures.items():
 p=base/(name+'.py');p.write_text(code+'\n')
 try:run_candidate(p,s)
 except (AssertionError,KeyError) as e:print(json.dumps({'fixture':name,'rejected':True,'reason':str(e)}),flush=True)
 else:raise AssertionError(name)
