# lean-sql-opt

Lean 4 (`v4.30.0`) 上で構築した、**全最適化ルールに形式等価性証明を必須化する SQL クエリリライタ**および PostgreSQL 17 向け TPC-DS 風ベンチマーク実験リポジトリです。

標準ライブラリのみ（外部依存パッケージなし）で実装されており、すべての登録ルールが `sorry` や独自 `axiom` を使わずに正当性を証明されています。

---

## 特徴と形式検証の仕組み

* **証明なしのルール登録を型で禁止 ([`VerifiedRule`](LeanSqlOpt/VerifiedRule.lean))**
  各書き換えルールは `step` 関数に加えて、以下の 2 つの証明フィールドを構造体として必須とします。
  * `preservesCols`: 書き換え前後で出力スキーマ（列名リスト）が不変であること
  * `sound`: `ValidDB schema db`（`NOT NULL`・`UNIQUE`・外部キー制約を満たす任意のデータベース状態）において、書き換え前後の評価結果が Bag（多重集合 / `List.Perm`）として同値であること
* **全体の健全性定理 (`optimizeWithLog_sound`)**
  複数ステップ・複数ルールを組み合わせた固定点ループ `optimizeWithLog` 全体についても、結果の列保存性と Bag 等価性が証明されています。
* **SQL 3値論理 (`TriBool`) の厳密モデル化 ([`SqlAst.lean`](LeanSqlOpt/SqlAst.lean), [`Semantics.lean`](LeanSqlOpt/Semantics.lean))**
  `TRUE` / `FALSE` / `UNKNOWN`（`NULL` 比較・否定・`IS NOT TRUE`・`IS DISTINCT FROM` 等）をモデル化し、`NULL` を含むデータでも壊れない最適化条件を証明しています。

---

## 実装済みの証明付き最適化ルール（計 10 本）

### 基本ルール（6 本: [`BaseRules.lean`](LeanSqlOpt/BaseRules.lean)）

| ルール ID | 内容 |
| --- | --- |
| `base.remove_true_filter` | 恒真述語 `WHERE TRUE` の除去 |
| `base.push_filter_join_left` | `INNER JOIN` 左辺のみを参照するフィルタのプッシュダウン |
| `base.push_filter_join_right` | `INNER JOIN` 右辺のみを参照するフィルタのプッシュダウン |
| `base.push_filter_and_join_left` | `AND` 条件の左辺参照側だけを `INNER JOIN` 左辺へ分割プッシュダウン |
| `base.push_filter_and_join_right` | `AND` 条件の右辺参照側だけを `INNER JOIN` 右辺へ分割プッシュダウン |
| `base.filter_merge` | 隣接する二重 `Filter` の `AND` 統合 |

### 高速化ルール（4 本: [`PerfRules.lean`](LeanSqlOpt/PerfRules.lean)）

| ルール ID | 狙いと内容 |
| --- | --- |
| `perf.eager_agg_through_join` | **Eager Aggregation**: ファクト表と次元表の `INNER JOIN` 前に、結合キーで事前 `GROUP BY` 集約をプッシュダウン（`SUM` / `COUNT` / `COUNT(*)` / `MIN` / `MAX`、多重適用防止ガード `isNotGroupBy` 付き） |
| `perf.elim_redundant_fk_join` | **冗長 FK JOIN 除去**: `NOT NULL` 外部キーと参照先 `UNIQUE` 制約があり、射影が参照先列を参照しない場合に不要な `INNER JOIN` を削除 |
| `perf.split_or_to_union_all` | **3値論理対応 `OR` → `UNION ALL` 分解**: `p OR q` を `p` と `q AND (p IS NOT TRUE)` の 2 ブランチへ排他分割し、インデックス適用可能なフィルタプッシュダウンを誘発 |
| `perf.decorrelate_scalar_agg_subquery` | **相関スカラー集約サブクエリのデコレレーション**: 空グループ時に `NULL` となる相関集約（`AVG` / `SUM` / `MIN` / `MAX`）を用いたフィルタを、`GROUP BY` + `INNER JOIN` へ変換 |

---

## ディレクトリ構成

```text
lean-sql-opt/
├── lean-toolchain               # Lean 4.30.0
├── lakefile.toml                # Lake ビルド設定
├── LeanSqlOpt.lean              # ライブラリルート
├── Main.lean                    # ベンチマーク対象 Q1〜Q6 の書き換え・--json 出力 CLI
├── LeanSqlOpt/
│   ├── SqlAst.lean              # AST (Val, TriBool, Expr, Pred, Query, Schema)
│   ├── Semantics.lean           # Bag 意味論 (List.Perm), ValidDB, 合同補題
│   ├── VerifiedRule.lean        # VerifiedRule 構造体と optimizeWithLog_sound
│   ├── BaseRules.lean           # 基本ルール 6 本 + 証明
│   ├── PerfRules.lean           # 高速化ルール 4 本 + 証明
│   ├── SqlPrint.lean            # PostgreSQL 向け SQL 生成 (toSql)
│   └── BenchQueries.lean        # TPC-DS 風スキーマ定義・検証クエリ Q1〜Q6
├── bench/                       # PostgreSQL 17 検証・計測用スキーマとスクリプト
│   ├── schema.sql               # store_sales 等 6 テーブル定義 (PK / NOT NULL / FK)
│   ├── load_data.sql            # store_sales 200 万行投入 + INDEX 6 本 + VACUUM ANALYZE
│   ├── prepare_bench.py         # Lean CLI から等価性検証・計測・EXPLAIN SQL を生成
│   └── analyze_bench.py         # CSV Bag 一致検証・中央値集計・EXPLAIN 解析
├── docs/                        # 設計計画・タスクリスト
└── backlog/                     # Backlog.md CLI タスク管理データ (LSO-1..LSO-6)
```

---

## ビルド・実行方法

### 1. Lean 4 証明の検証とビルド

```bash
lake build
```

`sorry` や `axiom` の不在確認:

```bash
rg -n "sorry|\baxiom\b" LeanSqlOpt Main.lean
```

### 2. SQL 書き換え結果の確認

```bash
# 人間向けの読みやすい形式で Q1〜Q6 の適用ルールと変換前後の SQL を表示
.lake/build/bin/lean-sql-opt

# ベンチマーク生成スクリプト向けの JSON 出力
.lake/build/bin/lean-sql-opt --json
```

### 3. ベンチマーク用 SQL の再生成

```bash
python3 bench/prepare_bench.py
```

---

## 現在の進捗と位置づけ（Backlog 状態）

プロジェクトの進捗は [Backlog.md](https://github.com/backlog-md/backlog.md) (`LSO-*`) で管理しています。

* **完了済み (`Done`)**
  * `LSO-1`: Lean 4 証明付き SQL リライタ基盤および全 10 ルールの実装・`lake build` 確認（20 jobs 成功・警告なし、`sorry`/`axiom` 0 件）
  * `LSO-2`: 分離した PostgreSQL 17 コンテナへの TPC-DS 風スタースキーマ（`store_sales` 200 万行等）投入および検証スクリプト整備
* **未実施 (`To Do`)**
  * `LSO-3`: PostgreSQL 17 実機での結果完全一致（Bag 等価性）検証
  * `LSO-4`: PostgreSQL 17 実行時間ベンチマーク計測
  * `LSO-5`: `EXPLAIN (ANALYZE, BUFFERS)` 分析と必要に応じた改善
  * `LSO-6`: 実測レポート (`docs/walkthrough.md`) 作成と環境の後片付け

### 前提と制限事項

* 本リポジトリは PostgreSQL の C 言語製プランナ本体を書き換えるものではなく、外部で AST を等価変換して PostgreSQL 互換 SQL を出力する**アプローチ（外付けリライタ）のプロトタイプ**です。
* 対象 SQL サブセットは `SqlAst.lean` でモデル化した範囲（単一カラム等値結合、`INNER` / `LEFT JOIN`、対応集約演算子など）に限られ、公式 TPC-DS 全 99 クエリ全体を網羅するものではありません。
* PostgreSQL 17 実機での速度向上率・結果一致の計測検証（`LSO-3`〜`LSO-5`）はまだ実施前であり、現時点で実機上の高速化率は未計測です。
