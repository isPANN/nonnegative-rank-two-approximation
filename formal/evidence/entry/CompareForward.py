import importlib.util
import json
from fractions import Fraction
from pathlib import Path

entry = Path(__file__).resolve().parent
repository = entry.parents[2]
spec = importlib.util.spec_from_file_location("candidate", repository / "algorithm/algorithm.py")
candidate = importlib.util.module_from_spec(spec)
spec.loader.exec_module(candidate)
rows = [json.loads(line) for line in (entry / "forward-outputs.jsonl").read_text().splitlines()]
results = []
for row in rows:
    expected = candidate.forward(row["source"])
    actual = row["target"]
    lhs = [[Fraction(x) for x in values] for values in actual["X"]]
    rhs = [[Fraction(x) for x in values] for values in expected["X"]]
    assert lhs == rhs, row["source"]
    assert Fraction(actual["tau"]) == Fraction(expected["tau"]), row["source"]
    results.append({"source": row["source"], "dimension": len(lhs),
                    "matrix_exact_match": True, "threshold_exact_match": True})
assert len(results) == 6
(entry / "forward-comparison.json").write_text(json.dumps({
    "cases": results, "status": "passed",
    "scope": "Finite exact-rational forward-map comparison; not a proof of Python/Z3 implementation agreement."
}, indent=2) + "\n")
print("All 6 Lean/Python forward constructions match entrywise and in threshold.")
