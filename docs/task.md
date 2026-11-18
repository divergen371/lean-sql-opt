# タスクリスト (Backlog): Lean 4 証明付き SQL オプティマイザ実験

## フェーズ 1: 環境・設計準備
- [x] Lean 4 (4.30.0) および Lake (5.0.0) の動作確認
- [x] Docker / Kiri 環境と既存 `postgres:17` イメージの確認
- [x] プロジェクト設計 (`implementation_plan.md`)・タスクリスト作成

## フェーズ 2: Lean 4 証明付き SQL リライタの実装
- [x] Lean 4 プロジェクト (`lean-sql-opt`) の初期化 (`SqlAst.lean`, `Semantics.lean`, `VerifiedRule.lean`, `BaseRules.lean`, `PerfRules.lean`, `SqlPrint.lean`, `BenchQueries.lean`, `Main.lean`)
- [x] SQL AST・3値論理 (`TriBool`)・値型・スキーマ制約の定義 (`SqlAst.lean`)
- [x] Bag 意味論 (`List.Perm`) と評価関数・`ValidDB` の定義 (`Semantics.lean`)
- [x] `VerifiedRule`（`preservesCols` + `sound`）とオプティマイザ全体健全性定理 (`optimizeWithLog_sound`) の実装 (`VerifiedRule.lean`)
- [x] 基本最適化ルール 6 本（すべて `sorry` なし証明付き）の実装 (`BaseRules.lean`: `removeTrueFilterRule`, `pushFilterJoinLeftRule`, `pushFilterJoinRightRule`, `pushFilterAndJoinLeftRule`, `pushFilterAndJoinRightRule`, `filterMergeRule`)
- [x] 高速化用 4 ルール（すべて `sorry` なし証明付き）の実装 (`PerfRules.lean`)
  - [x] `perf.eager_agg_through_join`: 結合前の事前集約プッシュダウン（多重適用防止ガード `isNotGroupBy` 追加済み）
  - [x] `perf.elim_redundant_fk_join`: 外部キー・NOT NULL・一意制約による冗長 `JOIN` 除去
  - [x] `perf.split_or_to_union_all`: 3値論理対応 (`IS NOT TRUE`) による `OR` → `UNION ALL` 分解
  - [x] `perf.decorrelate_scalar_agg_subquery`: 相関スカラー集約サブクエリのデコレレーション（`GROUP BY` + `JOIN` 化）
- [x] PostgreSQL SQL 出力・ベンチマーク対象クエリ Q1〜Q6 定義 (`SqlPrint.lean`, `BenchQueries.lean`, `Main.lean`)
- [x] `lake build` 成功（20 ジョブ・警告なし）、`sorry` / `axiom` 0 件、Q1〜Q6 の書き換えログ確認

## フェーズ 3: PostgreSQL 17 (コンテナ) でのベンチマーク・妥当性検証
### 完了済み
- [x] 実験専用 `postgres:17` コンテナ (`lean-pg17-bench`, `127.0.0.1:5439->5432`, `--shm-size=512m`) の起動
- [x] スキーマ作成 (`bench/schema.sql`)・TPC-DS 風データ投入 (`bench/load_data.sql`: `store_sales` 2,000,000 行等、インデックス 6 本、`VACUUM ANALYZE`)
- [x] ベンチマーク・比較解析スクリプト準備 (`bench/prepare_bench.py`, `bench/analyze_bench.py`, `bench/queries.json`, `bench/bench_equiv.sql`, `bench/bench_timing.sql`, `bench/bench_explain.sql`) およびコンテナ `/tmp/` への配置・`/tmp/bench_out` 作成

### 残りの ToDo (Backlog)
- [ ] **ToDo 1: 結果完全一致（Bag 等価性）の検証実行**
  - `lean-pg17-bench` 上で `/tmp/bench_equiv.sql` を実行し、全 6 クエリ × 3 形態 (`orig`, `base`, `full`) の CSV を `bench/out/` へ取得して一致確認
- [ ] **ToDo 2: 実行時間ベンチマークの計測**
  - `lean-pg17-bench` 上で `/tmp/bench_timing.sql`（グローバルウォームアップ 2 回 + インターリーブ 5 ラウンド）を実行し、`timings.csv` を取得
- [ ] **ToDo 3: `EXPLAIN (ANALYZE, BUFFERS)` 取得と定量分析・必要に応じた改善**
  - `/tmp/bench_explain.sql` を実行し、`bench/out/` 回収後に `python3 bench/analyze_bench.py` で速度比・実行計画を確認（1.5x〜2.5x 目標に対する到達度やボトルネックを評価し、必要なら Lean 側ルール／検証クエリを見直し・再ビルド・再計測）
- [ ] **ToDo 4: 検証レポート (`walkthrough.md`) 作成・コンテナ後片付け検討**
  - 実測結果と制約・限界を `docs/walkthrough.md` に記録（必要なら `lean-pg17-bench` の停止・削除を確認）
