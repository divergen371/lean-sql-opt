---
id: LSO-4
title: PostgreSQL 17 実行時間ベンチマーク計測
status: To Do
assignee: []
created_date: '2026-11-18T18:06:00Z'
labels: []
dependencies:
  - LSO-3
documentation:
  - docs/implementation_plan.md
  - docs/task.md
priority: high
type: task
ordinal: 4000
---

## Description

<!-- SECTION:DESCRIPTION:BEGIN -->
キャッシュや実行順バイアスを抑えたウォームアップとインターリーブ計測により、最適化前 (orig)・基本ルール (base)・全ルール (full) の実測レイテンシを取得する。
<!-- SECTION:DESCRIPTION:END -->

## Acceptance Criteria
<!-- AC:BEGIN -->
- [ ] #1 lean-pg17-bench 上で /tmp/bench_timing.sql を実行し 5 ラウンド分の timings.csv を bench/out へ回収できる
- [ ] #2 全 6 クエリの orig / base / full 各中央値と合計・幾何平均速度比が欠損なく算出される
<!-- AC:END -->
