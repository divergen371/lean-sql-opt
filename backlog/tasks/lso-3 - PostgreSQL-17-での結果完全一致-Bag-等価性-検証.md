---
id: LSO-3
title: PostgreSQL 17 での結果完全一致 (Bag 等価性) 検証
status: To Do
assignee: []
created_date: '2026-11-18T18:06:00Z'
labels: []
dependencies:
  - LSO-1
  - LSO-2
documentation:
  - docs/implementation_plan.md
  - docs/task.md
priority: high
type: task
ordinal: 3000
---

## Description

<!-- SECTION:DESCRIPTION:BEGIN -->
Lean 4 で形式証明された Bag 等価性が、実際の PostgreSQL 17 上で NULL 含む 200万行データに対して生成 SQL を実行した結果でも完全に成り立つかを検証する。
<!-- SECTION:DESCRIPTION:END -->

## Acceptance Criteria
<!-- AC:BEGIN -->
- [ ] #1 lean-pg17-bench 上で /tmp/bench_equiv.sql を実行し全 6 クエリ x 3 形態 (orig, base, full) の CSV を bench/out へ回収できる
- [ ] #2 bench/analyze_bench.py の結果比較で全 6 クエリにおいて orig == base および orig == full が True となる
<!-- AC:END -->
