import sys,json; print(json.dumps([False] if "--extract" in sys.argv else {"X":[[0]],"tau":0}))
