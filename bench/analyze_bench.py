import csv
import json
import math
import pathlib
import statistics
from collections import Counter, defaultdict

ROOT = pathlib.Path(__file__).resolve().parent.parent
BENCH = ROOT / "bench"
OUT = BENCH / "out"


def load_bag(path: pathlib.Path):
    with path.open("r", encoding="utf-8", newline="") as f:
        reader = csv.reader(f)
        header = next(reader)
        rows = [tuple(r) for r in reader]
    return header, Counter(rows), len(rows)


def summarize_plan(node: dict, depth: int = 0) -> list[str]:
    indent = "  " * depth
    ntype = node.get("Node Type", "?")
    rel = node.get("Relation Name")
    alias = node.get("Alias")
    extra = f" on {rel}" + (f" ({alias})" if alias and alias != rel else "") if rel else ""
    t_ms = node.get("Actual Total Time", 0.0)
    rows = node.get("Actual Rows", 0)
    loops = node.get("Actual Loops", 1)
    lines = [f"{indent}- {ntype}{extra} [time={t_ms:.2f}ms, rows={rows}, loops={loops}]"]
    for child in node.get("Plans", []):
        lines.extend(summarize_plan(child, depth + 1))
    return lines


def load_explain(path: pathlib.Path):
    data = json.loads(path.read_text(encoding="utf-8"))
    top = data[0]
    return {
        "planning_ms": top.get("Planning Time"),
        "execution_ms": top.get("Execution Time"),
        "plan": top.get("Plan", {}),
    }


def main() -> None:
    queries = json.loads((BENCH / "queries.json").read_text(encoding="utf-8"))

    print("=== 1. Bag Equivalence Verification (PostgreSQL 17 Actual Results) ===")
    all_equiv = True
    for q in queries:
        qid = q["id"]
        h_o, bag_o, n_o = load_bag(OUT / f"res_{qid}__orig.csv")
        h_b, bag_b, n_b = load_bag(OUT / f"res_{qid}__base.csv")
        h_f, bag_f, n_f = load_bag(OUT / f"res_{qid}__full.csv")
        ok_b = (h_o == h_b) and (bag_o == bag_b)
        ok_f = (h_o == h_f) and (bag_o == bag_f)
        if not (ok_b and ok_f):
            all_equiv = False
        print(f"  {qid}: rows={n_o} | orig==base: {ok_b} (rows={n_b}) | orig==full: {ok_f} (rows={n_f})")
        if not ok_b:
            print(f"    DIFF orig-base sample: {list((bag_o - bag_b).items())[:2]} / {list((bag_b - bag_o).items())[:2]}")
        if not ok_f:
            print(f"    DIFF orig-full sample: {list((bag_o - bag_f).items())[:2]} / {list((bag_f - bag_o).items())[:2]}")

    print(f"Overall equivalence match: {all_equiv}\n")

    timings: dict[tuple[str, str], list[float]] = defaultdict(list)
    with (OUT / "timings.csv").open("r", encoding="utf-8", newline="") as f:
        reader = csv.DictReader(f)
        for row in reader:
            timings[(row["qid"], row["variant"])].append(float(row["elapsed_ms"]))

    print("=== 2. Execution Timing Comparison (5 interleaved rounds after 2x global warmup) ===")
    total_orig = 0.0
    total_base = 0.0
    total_full = 0.0
    ratios_full = []
    ratios_base = []

    for q in queries:
        qid = q["id"]
        o_vals = timings[(qid, "orig")]
        b_vals = timings[(qid, "base")]
        f_vals = timings[(qid, "full")]
        o_med = statistics.median(o_vals)
        b_med = statistics.median(b_vals)
        f_med = statistics.median(f_vals)
        total_orig += o_med
        total_base += b_med
        total_full += f_med
        sp_base = o_med / b_med if b_med > 0 else 0.0
        sp_full = o_med / f_med if f_med > 0 else 0.0
        sp_perf_over_base = b_med / f_med if f_med > 0 else 0.0
        ratios_full.append(sp_full)
        ratios_base.append(sp_base)
        print(
            f"  {qid}:\n"
            f"    orig med={o_med:8.3f}ms  runs={o_vals}\n"
            f"    base med={b_med:8.3f}ms  runs={b_vals}  (vs orig: {sp_base:.2f}x) rules={q['base_rules']}\n"
            f"    full med={f_med:8.3f}ms  runs={f_vals}  (vs orig: {sp_full:.2f}x, vs base: {sp_perf_over_base:.2f}x) rules={q['full_rules']}"
        )

    geomean_full = math.exp(sum(math.log(x) for x in ratios_full) / len(ratios_full))
    geomean_base = math.exp(sum(math.log(x) for x in ratios_base) / len(ratios_base))
    print(f"\nSuite Total Median Time: orig={total_orig:.3f}ms, base={total_base:.3f}ms, full={total_full:.3f}ms")
    print(f"Suite Total Speedup (full vs orig): {total_orig / total_full:.2f}x (base vs orig: {total_orig / total_base:.2f}x, full vs base: {total_base / total_full:.2f}x)")
    print(f"Geometric Mean Speedup: full vs orig = {geomean_full:.2f}x, base vs orig = {geomean_base:.2f}x\n")

    print("=== 3. EXPLAIN (ANALYZE, BUFFERS) Summary ===")
    for q in queries:
        qid = q["id"]
        eo = load_explain(OUT / f"explain_{qid}__orig.json")
        ef = load_explain(OUT / f"explain_{qid}__full.json")
        print(f"--- {qid} ---")
        print(f"  [ORIG] plan={eo['planning_ms']:.2f}ms exec={eo['execution_ms']:.2f}ms")
        for line in summarize_plan(eo["plan"]):
            print("   " + line)
        print(f"  [FULL] plan={ef['planning_ms']:.2f}ms exec={ef['execution_ms']:.2f}ms")
        for line in summarize_plan(ef["plan"]):
            print("   " + line)


if __name__ == "__main__":
    main()
