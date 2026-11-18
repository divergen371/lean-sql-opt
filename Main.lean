import LeanSqlOpt

open LeanSqlOpt

/-- JSON 用文字列エスケープ -/
private def jsonEscape (s : String) : String :=
  let s1 := s.replace "\\" "\\\\"
  let s2 := s1.replace "\"" "\\\""
  let s3 := s2.replace "\n" "\\n"
  s3.replace "\r" "\\r"

private def strListJson (xs : List String) : String :=
  let items := xs.map (fun s => s!"\"{jsonEscape s}\"")
  "[" ++ joinList ", " items ++ "]"

def main (args : List String) : IO Unit := do
  if args.contains "--json" then
    IO.println "["
    let mut first := true
    for bq in allBenchQueries do
      let origSql := toSql bq.query
      let (baseOptQ, baseLogs) := optimizeWithLog 30 tpcdsSchema baseRules bq.query
      let baseSql := toSql baseOptQ
      let (fullOptQ, fullLogs) := optimizeWithLog 30 tpcdsSchema allRules bq.query
      let fullSql := toSql fullOptQ
      if !first then IO.println ","
      first := false
      IO.println "  {"
      IO.println s!"    \"id\": \"{jsonEscape bq.id}\","
      IO.println s!"    \"title\": \"{jsonEscape bq.title}\","
      IO.println s!"    \"orig_sql\": \"{jsonEscape origSql}\","
      IO.println s!"    \"base_sql\": \"{jsonEscape baseSql}\","
      IO.println s!"    \"base_rules\": {strListJson baseLogs},"
      IO.println s!"    \"full_sql\": \"{jsonEscape fullSql}\","
      IO.println s!"    \"full_rules\": {strListJson fullLogs}"
      IO.print "  }"
    IO.println ""
    IO.println "]"
  else
    IO.println s!"Lean 4 証明付き SQL オプティマイザ (登録ルール総数: {allRules.length} = 基本 {baseRules.length} + 追加 {perfRules.length})"
    for bq in allBenchQueries do
      let (fullOptQ, fullLogs) := optimizeWithLog 30 tpcdsSchema allRules bq.query
      IO.println s!"=== {bq.id}: {bq.title} ==="
      IO.println s!"適用ルール: {fullLogs}"
      IO.println s!"最適化前 SQL:\n{toSql bq.query}"
      IO.println s!"最適化後 SQL:\n{toSql fullOptQ}"
      IO.println ""
