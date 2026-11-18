---
id: LSO-2
title: PostgreSQL 17 実験コンテナ構築と 200万行 TPC-DS 風データ・検証スクリプト準備
status: Done
assignee:
  - '@antigravity'
created_date: '2026-11-18T18:05:00Z'
updated_date: '2026-11-18T18:05:00Z'
labels: []
dependencies:
  - LSO-1
documentation:
  - docs/implementation_plan.md
  - docs/task.md
priority: high
type: task
ordinal: 2000
---

## Description

<!-- SECTION:DESCRIPTION:BEGIN -->
既存コンテナに影響を与えない専用の PostgreSQL 17 コンテナを起動し、スタースキーマ 200万行の検証データおよび結果検証・計測用スクリプトを整備する。
<!-- SECTION:DESCRIPTION:END -->

## Acceptance Criteria
<!-- AC:BEGIN -->
- [x] #1 専用コンテナ lean-pg17-bench (postgres:17, port 5439) が起動し pg_isready 成功を確認する
- [x] #2 schema.sql と load_data.sql により store_sales 2,000,000 行を含む 6 テーブルとインデックス 6 本および VACUUM ANALYZE を完了する
- [x] #3 prepare_bench.py / analyze_bench.py と SQL スクリプト 3 本を準備しコンテナ内 /tmp へ配置する
<!-- AC:END -->

## Implementation Notes

<!-- SECTION:NOTES:BEGIN -->
2026-11-19 実測: lean-pg17-bench (127.0.0.1:5439->5432, shm 512m) 起動済み。date_dim 3,650 / item 20,000 / customer 50,000 / store 200 / promotion 500 / store_sales 2,000,000 行投入および INDEX 6本・VACUUM ANALYZE 完了。bench/ を lean-sql-opt 直下へ移動後も prepare_bench.py 正常実行確認済み。
<!-- SECTION:NOTES:END -->

## Final Summary

<!-- SECTION:FINAL_SUMMARY:BEGIN -->
実機 PostgreSQL 17 上での等価性検証および性能計測に必要な分離コンテナ、200万行データセット、NULL 混在データ、ベンチマーク生成・解析基盤を構築した。
<!-- SECTION:FINAL_SUMMARY:END -->
