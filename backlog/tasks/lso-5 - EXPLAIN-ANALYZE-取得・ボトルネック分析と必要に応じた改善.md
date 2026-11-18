---
id: LSO-5
title: EXPLAIN ANALYZE 取得・ボトルネック分析と必要に応じた改善
status: To Do
assignee: []
created_date: '2026-11-18T18:06:00Z'
labels: []
dependencies:
  - LSO-4
documentation:
  - docs/implementation_plan.md
  - docs/task.md
priority: medium
type: enhancement
ordinal: 5000
---

## Description

<!-- SECTION:DESCRIPTION:BEGIN -->
目標の 1.5x〜2.5x 高速化に対しどのルールが有効に働きどこが PostgreSQL 17 ネイティブ最適化と競合したかを物理実行計画で分析し、必要ならルールや検証設計を改善・再計測する。
<!-- SECTION:DESCRIPTION:END -->

## Acceptance Criteria
<!-- AC:BEGIN -->
- [ ] #1 bench_explain.sql を実行し全クエリ orig/full の EXPLAIN (ANALYZE, BUFFERS, FORMAT JSON) を取得・解析する
- [ ] #2 各クエリの高速化・悪化要因を実行計画ノードとバッファ統計に基づいて特定する
- [ ] #3 改善を加えた場合は lake build・sorry 0 件・等価性テスト・再ベンチマークまで再実行する
<!-- AC:END -->
