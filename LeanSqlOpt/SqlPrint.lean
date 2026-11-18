import LeanSqlOpt.PerfRules

namespace LeanSqlOpt

def escapeSqlStr (s : String) : String :=
  s.replace "'" "''"

def valToSql : Val → String
  | .null => "NULL"
  | .int n => toString n
  | .str s => s!"'{escapeSqlStr s}'"

def exprToSql : Expr → String
  | .col c => c
  | .lit v => valToSql v
  | .add e1 e2 => s!"({exprToSql e1} + {exprToSql e2})"
  | .mul e1 e2 => s!"({exprToSql e1} * {exprToSql e2})"

def predToSql : Pred → String
  | .trueLit => "TRUE"
  | .falseLit => "FALSE"
  | .eq e1 e2 => s!"({exprToSql e1} = {exprToSql e2})"
  | .ne e1 e2 => s!"({exprToSql e1} <> {exprToSql e2})"
  | .gt e1 e2 => s!"({exprToSql e1} > {exprToSql e2})"
  | .lt e1 e2 => s!"({exprToSql e1} < {exprToSql e2})"
  | .isNull e => s!"({exprToSql e} IS NULL)"
  | .isNotNull e => s!"({exprToSql e} IS NOT NULL)"
  | .isDistinctFrom e1 e2 => s!"({exprToSql e1} IS DISTINCT FROM {exprToSql e2})"
  | .not p => s!"(NOT {predToSql p})"
  | .notTrue p => s!"(({predToSql p}) IS NOT TRUE)"
  | .and p q => s!"({predToSql p} AND {predToSql q})"
  | .or p q => s!"({predToSql p} OR {predToSql q})"

def aggOpToSql (qualPrefix : String := "") : AggOp → String
  | .countStar => "COUNT(*)"
  | .countCol c => s!"COUNT({qualPrefix}{c})"
  | .sumCol c => s!"SUM({qualPrefix}{c})"
  | .avgCol c => s!"AVG({qualPrefix}{c})"
  | .minCol c => s!"MIN({qualPrefix}{c})"
  | .maxCol c => s!"MAX({qualPrefix}{c})"

def cmpOpToSql : CmpOp → String
  | .gt => ">"
  | .lt => "<"
  | .eq => "="

def joinList (sep : String) : List String → String
  | [] => ""
  | [x] => x
  | x :: xs => x ++ sep ++ joinList sep xs

private def freshSubAlias : StateM Nat String := do
  let n ← get
  set (n + 1)
  pure s!"_q{n}"

/-- Query AST を PostgreSQL 互換の実行可能 SQL に変換する -/
def queryToSqlM : Query → StateM Nat String
  | .scan table alias cols => do
    let proj := joinList ", " (cols.map fun c => s!"{alias}.{c} AS {qualCol alias c}")
    pure s!"SELECT {proj} FROM {table} AS {alias}"
  | .filter p inner => do
    let subSql ← queryToSqlM inner
    let subAlias ← freshSubAlias
    pure s!"SELECT * FROM ({subSql}) AS {subAlias} WHERE {predToSql p}"
  | .project items inner => do
    let subSql ← queryToSqlM inner
    let subAlias ← freshSubAlias
    let proj := joinList ", " (items.map fun it => s!"{exprToSql it.expr} AS {it.alias}")
    pure s!"SELECT {proj} FROM ({subSql}) AS {subAlias}"
  | .innerJoin l r cond => do
    let lSql ← queryToSqlM l
    let rSql ← queryToSqlM r
    let lAlias ← freshSubAlias
    let rAlias ← freshSubAlias
    pure s!"SELECT * FROM ({lSql}) AS {lAlias} INNER JOIN ({rSql}) AS {rAlias} ON {predToSql cond}"
  | .leftJoin l r cond => do
    let lSql ← queryToSqlM l
    let rSql ← queryToSqlM r
    let lAlias ← freshSubAlias
    let rAlias ← freshSubAlias
    pure s!"SELECT * FROM ({lSql}) AS {lAlias} LEFT JOIN ({rSql}) AS {rAlias} ON {predToSql cond}"
  | .groupBy keys aggs inner => do
    let subSql ← queryToSqlM inner
    let subAlias ← freshSubAlias
    let keyStrs := keys
    let aggStrs := aggs.map fun a => s!"{aggOpToSql "" a.op} AS {a.alias}"
    let sel := joinList ", " (keyStrs ++ aggStrs)
    let gb := joinList ", " keys
    pure s!"SELECT {sel} FROM ({subSql}) AS {subAlias} GROUP BY {gb}"
  | .unionAll l r => do
    let lSql ← queryToSqlM l
    let rSql ← queryToSqlM r
    pure s!"({lSql}) UNION ALL ({rSql})"
  | .corrAggFilter outer outerCmpCol cmp inner outerJoinCol innerJoinCol aggOp => do
    let oSql ← queryToSqlM outer
    let iSql ← queryToSqlM inner
    let oAlias ← freshSubAlias
    let iAlias ← freshSubAlias
    let aggSql := aggOpToSql s!"{iAlias}." aggOp
    pure s!"SELECT * FROM ({oSql}) AS {oAlias} WHERE {oAlias}.{outerCmpCol} {cmpOpToSql cmp} (SELECT {aggSql} FROM ({iSql}) AS {iAlias} WHERE {iAlias}.{innerJoinCol} = {oAlias}.{outerJoinCol})"

def toSql (q : Query) : String :=
  (queryToSqlM q).run' 0

end LeanSqlOpt
