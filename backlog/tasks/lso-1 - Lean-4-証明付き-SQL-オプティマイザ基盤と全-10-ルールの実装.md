---
id: LSO-1
title: Lean 4 証明付き SQL オプティマイザ基盤と全 10 ルールの実装
status: Done
assignee:
  - '@antigravity'
created_date: '2026-11-18T18:05:00Z'
updated_date: '2026-11-18T18:05:00Z'
labels: []
dependencies: []
documentation:
  - docs/implementation_plan.md
  - docs/task.md
priority: high
type: feature
ordinal: 1000
---

## Description

<!-- SECTION:DESCRIPTION:BEGIN -->
すべての書き換えルールに形式証明 (preservesCols + BagEq soundness) を必須化する Lean 4 SQL リライタを構築し、基本 6 ルールと高速化用 4 ルールを sorry/axiom なしで実装・検証する。
<!-- SECTION:DESCRIPTION:END -->

## Acceptance Criteria
<!-- AC:BEGIN -->
- [x] #1 SqlAst / Semantics / VerifiedRule により列保存性と Bag 意味論 (List.Perm) の全体健全性定理 optimizeWithLog_sound を実装する
- [x] #2 基本 6 ルール (BaseRules.lean) と高速化 4 ルール (PerfRules.lean) のすべてに sorry/axiom なしの証明を付与する
- [x] #3 lake build がエラー・警告なしで成功し、Q1〜Q6 の書き換え適用ログと出力 SQL を確認する
<!-- AC:END -->

## Implementation Notes

<!-- SECTION:NOTES:BEGIN -->
2026-11-19 実測: lake -d lean-sql-opt build 完了 (20 jobs, 警告なし)。rg -n "sorry|\baxiom\b" 0件。eagerAggThroughJoinRule へ多重適用防止ガード isNotGroupBy を追加し、BaseRules へ pushFilterAndJoinLeft/Right を追加して Q1〜Q6 の書き換え確認済み。
<!-- SECTION:NOTES:END -->

## Final Summary

<!-- SECTION:FINAL_SUMMARY:BEGIN -->
Lean 4.30.0 上に外部依存なしの証明付き SQL リライタを構築。全 10 ルール (基本 6 + 高速化 4) について 3値論理および Bag 意味論での等価性証明を完備し、ビルドと Q1〜Q6 変換出力まで確認した。
<!-- SECTION:FINAL_SUMMARY:END -->
