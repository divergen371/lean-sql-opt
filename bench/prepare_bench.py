import json
import pathlib
import subprocess

ROOT = pathlib.Path(__file__).resolve().parent.parent
BIN = ROOT / ".lake" / "build" / "bin" / "lean-sql-opt"
BENCH = ROOT / "bench"


def main() -> None:
    proc = subprocess.run([str(BIN), "--json"], capture_output=True, text=True, check=True)
    queries = json.loads(proc.stdout)
    (BENCH / "queries.json").write_text(json.dumps(queries, indent=2, ensure_ascii=False), encoding="utf-8")

    equiv_lines = []
    timing_lines = [
        "CREATE TEMP TABLE _bench_timings (qid TEXT, variant TEXT, round_idx INT, elapsed_ms NUMERIC);",
    ]
    explain_lines = [
        "\\pset tuples_only on",
        "\\pset format unaligned",
    ]

    # Note: dedup base/full when base_sql == orig_sql or full_sql == base_sql?
    # Still execute every variant verbatim so both equivalence and timings are directly measured.
    for q in queries:
        qid = q["id"]
        for variant in ("orig", "base", "full"):
            sql = q[f"{variant}_sql"].rstrip().rstrip(";")
            # SQL string literal escaping not needed for \copy query if no newlines;
            # single-line SQL from SqlPrint uses single quotes inside WHERE literals only,
            # whereas \copy ( ... ) takes raw SQL without string-literal quoting!
            equiv_lines.append(
                f"\\copy ({sql}) TO '/tmp/bench_out/res_{qid}__{variant}.csv' WITH (FORMAT CSV, HEADER true, NULL '__PG_NULL__')"
            )

    # Global buffer warmup (2x each orig/full)
    timing_lines.append("\\o /dev/null")
    for _ in range(2):
        for q in queries:
            for variant in ("orig", "base", "full"):
                sql = q[f"{variant}_sql"].rstrip().rstrip(";")
                timing_lines.append(f"{sql};")
    timing_lines.append("\\o")

    # 5 interleaved rounds per query to eliminate ordering/cache drift
    rounds = 5
    for q in queries:
        qid = q["id"]
        for r in range(1, rounds + 1):
            for variant in ("orig", "base", "full"):
                sql = q[f"{variant}_sql"].rstrip().rstrip(";")
                timing_lines.extend([
                    "SELECT extract(epoch FROM clock_timestamp()) AS t0 \\gset",
                    "\\o /dev/null",
                    f"{sql};",
                    "SELECT extract(epoch FROM clock_timestamp()) AS t1 \\gset",
                    "\\o",
                    f"INSERT INTO _bench_timings VALUES ('{qid}', '{variant}', {r}, round(((:t1 - :t0) * 1000.0)::numeric, 3));",
                ])

    timing_lines.append(
        "\\copy (SELECT qid, variant, round_idx, elapsed_ms FROM _bench_timings ORDER BY qid, variant, round_idx) TO '/tmp/bench_out/timings.csv' WITH (FORMAT CSV, HEADER true)"
    )

    for q in queries:
        qid = q["id"]
        for variant in ("orig", "full"):
            sql = q[f"{variant}_sql"].rstrip().rstrip(";")
            explain_lines.extend([
                f"\\o /tmp/bench_out/explain_{qid}__{variant}.json",
                f"EXPLAIN (ANALYZE, BUFFERS, FORMAT JSON) {sql};",
                "\\o",
            ])

    (BENCH / "bench_equiv.sql").write_text("\n".join(equiv_lines) + "\n", encoding="utf-8")
    (BENCH / "bench_timing.sql").write_text("\n".join(timing_lines) + "\n", encoding="utf-8")
    (BENCH / "bench_explain.sql").write_text("\n".join(explain_lines) + "\n", encoding="utf-8")
    print(f"Prepared {len(queries)} queries into {BENCH}")


if __name__ == "__main__":
    main()
