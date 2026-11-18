namespace LeanSqlOpt

/-- SQLのカラム名（修飾名または素のカラム名） -/
abbrev ColName := String

/-- テーブル名 -/
abbrev TableName := String

/-- SQL値（NULL, 整数, 文字列） -/
inductive Val where
  | null : Val
  | int : Int → Val
  | str : String → Val
  deriving DecidableEq, Repr

/-- SQLの3値論理（TRUE / FALSE / UNKNOWN） -/
inductive TriBool where
  | t : TriBool
  | f : TriBool
  | u : TriBool
  deriving DecidableEq, Repr

namespace TriBool

def and : TriBool → TriBool → TriBool
  | f, _ => f
  | _, f => f
  | t, t => t
  | _, _ => u

def or : TriBool → TriBool → TriBool
  | t, _ => t
  | _, t => t
  | f, f => f
  | _, _ => u

def not : TriBool → TriBool
  | t => f
  | f => t
  | u => u

/-- SQLの `IS NOT TRUE`（FALSE または UNKNOWN のとき TRUE） -/
def notTrue : TriBool → TriBool
  | t => f
  | f => t
  | u => t

def isTrue : TriBool → Bool
  | t => true
  | _ => false

end TriBool

/-- SQLスカラ式 -/
inductive Expr where
  | col : ColName → Expr
  | lit : Val → Expr
  | add : Expr → Expr → Expr
  | mul : Expr → Expr → Expr
  deriving DecidableEq, Repr, BEq

/-- SQL述語（WHERE / ON 条件） -/
inductive Pred where
  | trueLit : Pred
  | falseLit : Pred
  | eq : Expr → Expr → Pred
  | ne : Expr → Expr → Pred
  | gt : Expr → Expr → Pred
  | lt : Expr → Expr → Pred
  | isNull : Expr → Pred
  | isNotNull : Expr → Pred
  | isDistinctFrom : Expr → Expr → Pred
  | not : Pred → Pred
  | notTrue : Pred → Pred
  | and : Pred → Pred → Pred
  | or : Pred → Pred → Pred
  deriving DecidableEq, Repr, BEq

/-- 集約演算子 -/
inductive AggOp where
  | countStar : AggOp
  | countCol : ColName → AggOp
  | sumCol : ColName → AggOp
  | avgCol : ColName → AggOp
  | minCol : ColName → AggOp
  | maxCol : ColName → AggOp
  deriving DecidableEq, Repr, BEq

/-- 集約項目（集約演算子 + 出力列名） -/
structure AggItem where
  op : AggOp
  alias : ColName
  deriving DecidableEq, Repr, BEq

/-- 射影項目（式 + 出力列名） -/
structure ProjItem where
  expr : Expr
  alias : ColName
  deriving DecidableEq, Repr, BEq

/-- 相関サブクエリ比較演算子 -/
inductive CmpOp where
  | gt : CmpOp
  | lt : CmpOp
  | eq : CmpOp
  deriving DecidableEq, Repr, BEq

/-- 関係代数 / SQL クエリ AST -/
inductive Query where
  | scan : TableName → String → List ColName → Query
  | filter : Pred → Query → Query
  | project : List ProjItem → Query → Query
  | innerJoin : Query → Query → Pred → Query
  | leftJoin : Query → Query → Pred → Query
  | groupBy : List ColName → List AggItem → Query → Query
  | unionAll : Query → Query → Query
  | corrAggFilter :
      Query → ColName → CmpOp → Query → ColName → ColName → AggOp → Query
  deriving DecidableEq, Repr, BEq

/-- 外部キー制約（テーブル単位の素の列名で指定） -/
structure ForeignKey where
  srcTable : TableName
  srcCol : ColName
  dstTable : TableName
  dstCol : ColName
  deriving DecidableEq, Repr, BEq

/-- データベーススキーマ制約 -/
structure Schema where
  tableCols : TableName → List ColName
  notNull : TableName → ColName → Bool
  uniqueKey : TableName → ColName → Bool
  foreignKeys : List ForeignKey

/-- テーブルエイリアスと素の列名から内部修飾名を作成 -/
def qualCol (tableAlias col : String) : ColName :=
  tableAlias ++ "__" ++ col

end LeanSqlOpt
