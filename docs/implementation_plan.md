# 実装計画: Lean 4 証明付き SQL リライタと PostgreSQL 17 TPC-DS 準拠ベンチマーク

## 1. 目的とスコープ
PostgreSQL 本体の C 言語オプティマイザを直接書き換えるのではなく、PostgreSQL の手前で SQL を等価書き換えする **「全ルール Lean 4 証明付き SQL リライタ」** を構築し、TPC-DS 準拠スキーマ・クエリ群において **1.5倍〜2.5倍以上** の高速化が得られるかを実験・検証する。

### 保証する範囲（Lean 4 の形式証明）
- リライタに登録する最適化ルールはすべて `VerifiedRule` 型（書き換え関数 + 等価性証明を同梱）とする。
- SQL 意味論は **順序を問わない多重集合（Bag 意味論: `List.Perm`）** および **SQL の 3値論理（`TRUE` / `FALSE` / `UNKNOWN(NULL)`）** をモデル化する。
- `sorry` や未検証の公理を用いずに全ルールの健全性およびオプティマイザ全体の健全性定理を証明する。

## 2. 実装する最適化ルール
### 基本ルール（Base Rules）
- `filterMerge`: 連続する `Filter` の結合（`Filter p (Filter q r) -> Filter (p AND q) r`）
- `pushFilterJoinLeft`: 左側テーブルのみを参照する条件の `InnerJoin` 左辺へのプッシュダウン
- `pushFilterJoinRight`: 右側テーブルのみを参照する条件の `InnerJoin` 右辺へのプッシュダウン
- `removeTrueFilter`: 恒真条件フィルタの除去

### 追加の高速化用 4 ルール（Performance Rules）
1. **Eager Aggregation (`eagerAggThroughJoin`)**:
   - ファクト表 × ディメンション表の `JOIN` 後に `GROUP BY` する際、結合前の事前集約へ変換し、中間結合行数を削減する。
2. **冗長な外部キー結合の除去 (`elimRedundantFKJoin`)**:
   - スキーマの `NOT NULL` + `FOREIGN KEY` + `UNIQUE` 制約のもとで、出力や条件に参照されない結合先テーブルを安全に除去する。
3. **3値論理対応 `OR` → `UNION ALL` 排他分解 (`splitOrToUnionAll`)**:
   - `P OR Q` を `P` と `Q AND NOT_TRUE(P)` の `UNION ALL` に分割する。`NULL` 時に `NOT(P)` が `UNKNOWN` となって行が欠落するバグを防ぐため、`isTrue` 否定の厳密等価性を Lean で証明する。
4. **相関集約サブクエリのデコレレーション (`decorrelateScalarAggSubquery`)**:
   - `outer.val > (SELECT AGG(inner.val) FROM inner WHERE inner.k = outer.k)` 型の相関スカラー集約サブクエリを、`GROUP BY` 済みサブクエリとの `INNER JOIN` へ変換する（空グループ時に `NULL` となり厳格比較で落ちる性質を証明して適用）。

## 3. PostgreSQL 17 検証環境
- 既存コンテナ (`helpdesk_commander_postgres` 等) とは独立した新規コンテナ `lean-pg17-bench`（ポート `5439`）を `postgres:17` イメージから起動する。
- TPC-DS の主要スタースキーマ（`store_sales`, `date_dim`, `item`, `customer`, `store`, `promotion` 等）を構築し、統計情報（`ANALYZE`）と適切なインデックスを設定した上で、最適化前後の **出力一致確認** と **複数回計測による速度比較** を行う。
