import LeanSqlOpt.SqlAst

namespace LeanSqlOpt

/-- 行表現: カラム名から Option Val への写像 (none = スキーマ外の列, some .null = SQL NULL) -/
abbrev Row := ColName → Option Val

/-- 多重集合 (Bag) としてのテーブル・結果セット -/
abbrev Bag := List Row

/-- データベース状態: テーブル名から生行リストへの写像 -/
abbrev DB := TableName → List Row

namespace Row

def empty : Row := fun _ => none

def getVal (r : Row) (c : ColName) : Val :=
  (r c).getD .null

def merge (r1 r2 : Row) : Row :=
  fun c => match r1 c with
    | some v => some v
    | none => r2 c

def nullPad (cols : List ColName) : Row :=
  fun c => if c ∈ cols then some .null else none

end Row

/-- スカラ式評価 -/
def evalExpr (r : Row) : Expr → Val
  | .col c => Row.getVal r c
  | .lit v => v
  | .add e1 e2 =>
    match evalExpr r e1, evalExpr r e2 with
    | .int a, .int b => .int (a + b)
    | _, _ => .null
  | .mul e1 e2 =>
    match evalExpr r e1, evalExpr r e2 with
    | .int a, .int b => .int (a * b)
    | _, _ => .null

/-- SQL 3値論理に基づく述語評価 -/
def evalPred (r : Row) : Pred → TriBool
  | .trueLit => .t
  | .falseLit => .f
  | .eq e1 e2 =>
    match evalExpr r e1, evalExpr r e2 with
    | .null, _ => .u
    | _, .null => .u
    | v1, v2 => if v1 == v2 then .t else .f
  | .ne e1 e2 =>
    match evalExpr r e1, evalExpr r e2 with
    | .null, _ => .u
    | _, .null => .u
    | v1, v2 => if v1 != v2 then .t else .f
  | .gt e1 e2 =>
    match evalExpr r e1, evalExpr r e2 with
    | .int a, .int b => if a > b then .t else .f
    | .str a, .str b => if a > b then .t else .f
    | _, _ => .u
  | .lt e1 e2 =>
    match evalExpr r e1, evalExpr r e2 with
    | .int a, .int b => if a < b then .t else .f
    | .str a, .str b => if a < b then .t else .f
    | _, _ => .u
  | .isNull e =>
    if evalExpr r e == .null then .t else .f
  | .isNotNull e =>
    if evalExpr r e != .null then .t else .f
  | .isDistinctFrom e1 e2 =>
    if evalExpr r e1 != evalExpr r e2 then .t else .f
  | .not p => (evalPred r p).not
  | .notTrue p => (evalPred r p).notTrue
  | .and p q => (evalPred r p).and (evalPred r q)
  | .or p q => (evalPred r p).or (evalPred r q)

/-- 比較演算子評価 (相関サブクエリ比較用、NULLに対しては .u を返す) -/
def evalCmp (cmp : CmpOp) (v1 v2 : Val) : TriBool :=
  match v1, v2 with
  | .null, _ => .u
  | _, .null => .u
  | .int a, .int b =>
    match cmp with
    | .gt => if a > b then .t else .f
    | .lt => if a < b then .t else .f
    | .eq => if a == b then .t else .f
  | .str a, .str b =>
    match cmp with
    | .gt => if a > b then .t else .f
    | .lt => if a < b then .t else .f
    | .eq => if a == b then .t else .f
  | _, _ =>
    match cmp with
    | .eq => if v1 == v2 then .t else .f
    | _ => .u

/-- 射影行生成 -/
def evalProjItems (items : List ProjItem) (r : Row) : Row :=
  match items with
  | [] => fun _ => none
  | it :: rest =>
    fun c => if c == it.alias then some (evalExpr r it.expr) else evalProjItems rest r c

/-- 非NULL整数値の合計と個数を集計する補助関数 (Perm不変性のために foldr を利用) -/
def sumNonNullInts (col : ColName) : List Row → Option Int
  | [] => none
  | r :: rs =>
    match Row.getVal r col, sumNonNullInts col rs with
    | .int n, some acc => some (n + acc)
    | .int n, none => some n
    | _, acc => acc

def countNonNull (col : ColName) : List Row → Nat
  | [] => 0
  | r :: rs =>
    match Row.getVal r col with
    | .null => countNonNull col rs
    | _ => 1 + countNonNull col rs

def minNonNullInt (col : ColName) : List Row → Option Int
  | [] => none
  | r :: rs =>
    match Row.getVal r col, minNonNullInt col rs with
    | .int n, some m => some (min n m)
    | .int n, none => some n
    | _, acc => acc

def maxNonNullInt (col : ColName) : List Row → Option Int
  | [] => none
  | r :: rs =>
    match Row.getVal r col, maxNonNullInt col rs with
    | .int n, some m => some (max n m)
    | .int n, none => some n
    | _, acc => acc

/-- 集約演算子の評価 -/
def evalAgg (op : AggOp) (grp : List Row) : Val :=
  match op with
  | .countStar => .int grp.length
  | .countCol c => .int (countNonNull c grp)
  | .sumCol c =>
    match sumNonNullInts c grp with
    | some s => .int s
    | none => .null
  | .avgCol c =>
    match sumNonNullInts c grp, countNonNull c grp with
    | some s, k => if k == 0 then .null else .int (s / (k : Int))
    | none, _ => .null
  | .minCol c =>
    match minNonNullInt c grp with
    | some m => .int m
    | none => .null
  | .maxCol c =>
    match maxNonNullInt c grp with
    | some m => .int m
    | none => .null

/-- グループキー値タプル -/
def rowKey (keys : List ColName) (r : Row) : List Val :=
  keys.map (Row.getVal r)

/-- 順序保持の重複除去（後ろに同値要素があればスキップ） -/
def dedup [DecidableEq α] : List α → List α
  | [] => []
  | x :: xs => if x ∈ xs then dedup xs else x :: dedup xs

/-- グループキー列と集約項目から1行を構築 -/
def setColsFromPairs (pairs : List (ColName × Val)) : Row :=
  match pairs with
  | [] => fun _ => none
  | (k, v) :: rest => fun c => if c == k then some v else setColsFromPairs rest c

def buildGroupRow (keys : List ColName) (aggs : List AggItem) (keyVals : List Val) (grp : List Row) : Row :=
  let keyPairs := keys.zip keyVals
  let aggPairs := aggs.map (fun a => (a.alias, evalAgg a.op grp))
  setColsFromPairs (keyPairs ++ aggPairs)

/-- クエリの出力カラム名一覧（静的抽出） -/
def queryCols : Query → List ColName
  | .scan _ alias cols => cols.map (qualCol alias)
  | .filter _ q => queryCols q
  | .project items _ => items.map (·.alias)
  | .innerJoin l r _ => queryCols l ++ queryCols r
  | .leftJoin l r _ => queryCols l ++ queryCols r
  | .groupBy keys aggs _ => keys ++ aggs.map (·.alias)
  | .unionAll l r => queryCols l ++ (queryCols r).filter (fun c => !(c ∈ queryCols l))
  | .corrAggFilter o _ _ _ _ _ _ => queryCols o

/-- テーブル行にエイリアス修飾子を付与 -/
def qualifyRow (tableAlias : String) (cols : List ColName) (raw : Row) : Row :=
  match cols with
  | [] => fun _ => none
  | c :: cs =>
    fun col => if col == qualCol tableAlias c then raw c else qualifyRow tableAlias cs raw col

/-- クエリの Bag 意味論評価関数 -/
def eval (db : DB) : Query → Bag
  | .scan table alias cols =>
    (db table).map (qualifyRow alias cols)
  | .filter p q =>
    (eval db q).filter (fun r => (evalPred r p).isTrue)
  | .project items q =>
    (eval db q).map (evalProjItems items)
  | .innerJoin l r cond =>
    (eval db l).flatMap fun rl =>
      (eval db r).filterMap fun rr =>
        let m := Row.merge rl rr
        if (evalPred m cond).isTrue then some m else none
  | .leftJoin l r cond =>
    let rCols := queryCols r
    (eval db l).flatMap fun rl =>
      let matched := (eval db r).filterMap fun rr =>
        let m := Row.merge rl rr
        if (evalPred m cond).isTrue then some m else none
      if matched.isEmpty then
        [Row.merge rl (Row.nullPad rCols)]
      else
        matched
  | .groupBy keys aggs q =>
    let rows := eval db q
    let ks := dedup (rows.map (rowKey keys))
    ks.map fun k =>
      buildGroupRow keys aggs k (rows.filter fun r => rowKey keys r == k)
  | .unionAll l r =>
    eval db l ++ eval db r
  | .corrAggFilter outer outerCmpCol cmp inner outerJoinCol innerJoinCol aggOp =>
    let innerRows := eval db inner
    (eval db outer).filter fun ro =>
      let kv := Row.getVal ro outerJoinCol
      let grp := innerRows.filter fun ri =>
        match Row.getVal ri innerJoinCol, kv with
        | .null, _ => false
        | _, .null => false
        | v1, v2 => v1 == v2
      let av := evalAgg aggOp grp
      (evalCmp cmp (Row.getVal ro outerCmpCol) av).isTrue

/-- Bag 等価性（順序を問わない多重集合としての一致） -/
abbrev BagEq (b1 b2 : Bag) : Prop :=
  b1.Perm b2

/-- データベースがスキーマ制約を満たすことの定義 -/
structure ValidDB (schema : Schema) (db : DB) : Prop where
  /-- 各テーブルの行は schema.tableCols に記載された列のみを持つ -/
  colsMatch :
    ∀ t r, r ∈ db t → ∀ c, (r c).isSome ↔ c ∈ schema.tableCols t
  /-- NOT NULL 制約 -/
  notNullHolds :
    ∀ t c, schema.notNull t c = true →
      ∀ r ∈ db t, ∃ v, r c = some v ∧ v ≠ .null
  /-- UNIQUE 制約（同じ非NULL値を持つ行は最大1行） -/
  uniqueHolds :
    ∀ t c, schema.uniqueKey t c = true →
      ∀ v : Val, v ≠ .null →
        ((db t).filter (fun r => r c == some v)).length ≤ 1
  /-- FOREIGN KEY 制約（参照元が非NULLなら参照先に一致行が存在） -/
  fkHolds :
    ∀ fk ∈ schema.foreignKeys,
      ∀ r ∈ db fk.srcTable, ∀ v,
        r fk.srcCol = some v → v ≠ .null →
          ∃ r' ∈ db fk.dstTable, r' fk.dstCol = some v

/-! ### BagEq の基本性質とリスト補題 -/

theorem BagEq.refl (b : Bag) : BagEq b b :=
  List.Perm.refl b

theorem BagEq.symm {b1 b2 : Bag} (h : BagEq b1 b2) : BagEq b2 b1 :=
  List.Perm.symm h

theorem BagEq.trans {b1 b2 b3 : Bag} (h1 : BagEq b1 b2) (h2 : BagEq b2 b3) : BagEq b1 b3 :=
  List.Perm.trans h1 h2

theorem BagEq.filter {b1 b2 : Bag} (p : Row → Bool) (h : BagEq b1 b2) :
    BagEq (b1.filter p) (b2.filter p) :=
  List.Perm.filter p h

theorem BagEq.map {b1 b2 : Bag} (f : Row → Row) (h : BagEq b1 b2) :
    BagEq (b1.map f) (b2.map f) :=
  List.Perm.map f h

theorem BagEq.append {a1 a2 b1 b2 : Bag} (ha : BagEq a1 a2) (hb : BagEq b1 b2) :
    BagEq (a1 ++ b1) (a2 ++ b2) :=
  List.Perm.append ha hb

/-! ### List / Perm / 集約用の基礎補題 -/

theorem mem_dedup [DecidableEq α] {x : α} {xs : List α} :
    x ∈ dedup xs ↔ x ∈ xs := by
  induction xs with
  | nil => simp [dedup]
  | cons y ys ih =>
    simp only [dedup]
    split
    · rename_i hy
      constructor
      · intro h
        exact List.mem_cons_of_mem y (ih.mp h)
      · intro h
        rcases List.mem_cons.mp h with rfl | hys
        · exact ih.mpr hy
        · exact ih.mpr hys
    · rename_i hy
      simp [List.mem_cons, ih]

theorem nodup_dedup [DecidableEq α] (xs : List α) : (dedup xs).Nodup := by
  induction xs with
  | nil => simp [dedup]
  | cons y ys ih =>
    simp only [dedup]
    split
    · exact ih
    · rename_i hy
      rw [List.nodup_cons]
      exact ⟨fun h => hy (mem_dedup.mp h), ih⟩

theorem perm_of_nodup_mem_iff {xs ys : List α} (hx : xs.Nodup) (hy : ys.Nodup)
    (hmem : ∀ x, x ∈ xs ↔ x ∈ ys) : xs.Perm ys := by
  induction xs generalizing ys with
  | nil =>
    cases ys with
    | nil => exact List.Perm.nil
    | cons y ys =>
      have : y ∈ ([] : List α) := (hmem y).mpr (by simp)
      simp at this
  | cons x xs ih =>
    rw [List.nodup_cons] at hx
    have hx_in : x ∈ ys := (hmem x).mp (by simp)
    rcases List.append_of_mem hx_in with ⟨l1, l2, rfl⟩
    have hnodup_rest : (l1 ++ l2).Nodup := by
      have hy' := hy
      rw [List.nodup_append] at hy' ⊢
      rcases hy' with ⟨h1, h2, hdisj⟩
      rw [List.nodup_cons] at h2
      refine ⟨h1, h2.2, ?_⟩
      intro a ha1 b hb2
      exact hdisj a ha1 b (List.mem_cons_of_mem x hb2)
    have hx_not_in_rest : x ∉ l1 ++ l2 := by
      have hy' := hy
      rw [List.nodup_append] at hy'
      rcases hy' with ⟨_, h2, hdisj⟩
      rw [List.nodup_cons] at h2
      intro hmemx
      rcases List.mem_append.mp hmemx with h1 | h2'
      · exact hdisj x h1 x (List.mem_cons_self ..) rfl
      · exact h2.1 h2'
    have ih_perm : xs.Perm (l1 ++ l2) := by
      apply ih hx.2 hnodup_rest
      intro z
      constructor
      · intro hz
        have hzy : z ∈ l1 ++ x :: l2 := (hmem z).mp (List.mem_cons_of_mem x hz)
        rcases List.mem_append.mp hzy with h1 | h2
        · exact List.mem_append.mpr (Or.inl h1)
        · rcases List.mem_cons.mp h2 with rfl | h2'
          · exact False.elim (hx.1 hz)
          · exact List.mem_append.mpr (Or.inr h2')
      · intro hz
        have hz' : z ∈ l1 ++ x :: l2 := by
          rcases List.mem_append.mp hz with h1 | h2
          · exact List.mem_append.mpr (Or.inl h1)
          · exact List.mem_append.mpr (Or.inr (List.mem_cons_of_mem x h2))
        have hzx : z ∈ x :: xs := (hmem z).mpr hz'
        rcases List.mem_cons.mp hzx with rfl | hzxs
        · exact False.elim (hx_not_in_rest hz)
        · exact hzxs
    exact (ih_perm.cons x).trans List.perm_middle.symm

theorem perm_dedup [DecidableEq α] {xs ys : List α} (h : xs.Perm ys) :
    (dedup xs).Perm (dedup ys) := by
  apply perm_of_nodup_mem_iff (nodup_dedup xs) (nodup_dedup ys)
  intro x
  rw [mem_dedup, mem_dedup]
  exact h.mem_iff

theorem perm_filterMap {xs ys : List α} (f : α → Option β) (h : xs.Perm ys) :
    (xs.filterMap f).Perm (ys.filterMap f) := by
  induction h with
  | nil => exact List.Perm.nil
  | cons x _ ih =>
    simp only [List.filterMap]
    cases f x with
    | none => exact ih
    | some b => exact ih.cons b
  | swap x y zs =>
    simp only [List.filterMap]
    cases f x <;> cases f y <;> simp [List.Perm.swap]
  | trans _ _ ih1 ih2 => exact ih1.trans ih2

theorem perm_flatMap_congr (xs : List α) {f g : α → List β}
    (hfg : ∀ x, (f x).Perm (g x)) :
    (xs.flatMap f).Perm (xs.flatMap g) := by
  induction xs with
  | nil => exact List.Perm.nil
  | cons x xs' ih =>
    simp only [List.flatMap_cons]
    exact (hfg x).append ih

theorem perm_flatMap {xs ys : List α} (f g : α → List β)
    (h : xs.Perm ys) (hfg : ∀ x, (f x).Perm (g x)) :
    (xs.flatMap f).Perm (ys.flatMap g) := by
  have h1 : (xs.flatMap f).Perm (ys.flatMap f) := by
    induction h with
    | nil => exact List.Perm.nil
    | cons x _ ih =>
      simp only [List.flatMap_cons]
      exact (List.Perm.refl (f x)).append ih
    | swap x y zs =>
      simp only [List.flatMap_cons, ← List.append_assoc]
      exact List.Perm.append List.perm_append_comm (List.Perm.refl _)
    | trans _ _ ih1 ih2 => exact ih1.trans ih2
  exact h1.trans (perm_flatMap_congr ys hfg)

theorem sumNonNullInts_perm (col : ColName) {xs ys : List Row} (h : xs.Perm ys) :
    sumNonNullInts col xs = sumNonNullInts col ys := by
  induction h with
  | nil => rfl
  | cons x _ ih =>
    simp only [sumNonNullInts, ih]
  | swap x y zs =>
    simp only [sumNonNullInts]
    cases hx : Row.getVal x col <;> cases hy : Row.getVal y col <;> cases hz : sumNonNullInts col zs <;> simp
    all_goals omega
  | trans _ _ ih1 ih2 => exact ih1.trans ih2

theorem countNonNull_perm (col : ColName) {xs ys : List Row} (h : xs.Perm ys) :
    countNonNull col xs = countNonNull col ys := by
  induction h with
  | nil => rfl
  | cons x _ ih =>
    simp only [countNonNull]
    cases Row.getVal x col <;> simp [ih]
  | swap x y zs =>
    simp only [countNonNull]
    cases Row.getVal x col <;> cases Row.getVal y col <;> simp <;> omega
  | trans _ _ ih1 ih2 => exact ih1.trans ih2

theorem minNonNullInt_perm (col : ColName) {xs ys : List Row} (h : xs.Perm ys) :
    minNonNullInt col xs = minNonNullInt col ys := by
  induction h with
  | nil => rfl
  | cons x _ ih =>
    simp only [minNonNullInt, ih]
  | swap x y zs =>
    simp only [minNonNullInt]
    cases Row.getVal x col <;> cases Row.getVal y col <;> cases minNonNullInt col zs <;> simp
    all_goals omega
  | trans _ _ ih1 ih2 => exact ih1.trans ih2

theorem maxNonNullInt_perm (col : ColName) {xs ys : List Row} (h : xs.Perm ys) :
    maxNonNullInt col xs = maxNonNullInt col ys := by
  induction h with
  | nil => rfl
  | cons x _ ih =>
    simp only [maxNonNullInt, ih]
  | swap x y zs =>
    simp only [maxNonNullInt]
    cases Row.getVal x col <;> cases Row.getVal y col <;> cases maxNonNullInt col zs <;> simp
    all_goals omega
  | trans _ _ ih1 ih2 => exact ih1.trans ih2

theorem evalAgg_perm (op : AggOp) {xs ys : List Row} (h : xs.Perm ys) :
    evalAgg op xs = evalAgg op ys := by
  cases op with
  | countStar => simp [evalAgg, h.length_eq]
  | countCol c => simp [evalAgg, countNonNull_perm c h]
  | sumCol c => simp [evalAgg, sumNonNullInts_perm c h]
  | avgCol c => simp [evalAgg, sumNonNullInts_perm c h, countNonNull_perm c h]
  | minCol c => simp [evalAgg, minNonNullInt_perm c h]
  | maxCol c => simp [evalAgg, maxNonNullInt_perm c h]

theorem buildGroupRow_perm (keys : List ColName) (aggs : List AggItem) (k : List Val)
    {xs ys : List Row} (h : xs.Perm ys) :
    buildGroupRow keys aggs k xs = buildGroupRow keys aggs k ys := by
  simp only [buildGroupRow]
  congr 1
  congr 1
  apply List.map_congr_left
  intro a _
  simp [evalAgg_perm a.op h]

/-! ### 行ドメイン (queryCols) に関する不変条件 -/

theorem qualifyRow_dom (a : String) (cols : List ColName) (raw : Row) (c : ColName) :
    (qualifyRow a cols raw c).isSome → c ∈ cols.map (qualCol a) := by
  induction cols with
  | nil => simp [qualifyRow]
  | cons x xs ih =>
    simp only [qualifyRow, List.map_cons, List.mem_cons]
    split
    · rename_i heq
      intro _
      left
      exact (beq_iff_eq.mp heq)
    · intro hsome
      right
      exact ih hsome

theorem evalProjItems_dom (items : List ProjItem) (r : Row) (c : ColName) :
    (evalProjItems items r c).isSome → c ∈ items.map (·.alias) := by
  induction items with
  | nil => simp [evalProjItems]
  | cons it rest ih =>
    simp only [evalProjItems, List.map_cons, List.mem_cons]
    split
    · rename_i heq
      intro _
      left
      exact (beq_iff_eq.mp heq)
    · intro hsome
      right
      exact ih hsome

theorem setColsFromPairs_dom (pairs : List (ColName × Val)) (c : ColName) :
    (setColsFromPairs pairs c).isSome → c ∈ pairs.map Prod.fst := by
  induction pairs with
  | nil => simp [setColsFromPairs]
  | cons p ps ih =>
    rcases p with ⟨k, v⟩
    simp only [setColsFromPairs, List.map_cons, List.mem_cons]
    split
    · rename_i heq
      intro _
      left
      exact (beq_iff_eq.mp heq)
    · intro hsome
      right
      exact ih hsome

theorem Row.merge_dom {r1 r2 : Row} {c : ColName} :
    (Row.merge r1 r2 c).isSome → (r1 c).isSome ∨ (r2 c).isSome := by
  simp only [Row.merge]
  cases r1 c with
  | none => intro h; exact Or.inr h
  | some _ => intro _; exact Or.inl rfl

theorem eval_row_dom (db : DB) (q : Query) :
    ∀ r ∈ eval db q, ∀ c, (r c).isSome → c ∈ queryCols q := by
  induction q with
  | scan t a cols =>
    intro r hr c hc
    simp only [eval, List.mem_map] at hr
    rcases hr with ⟨raw, _, rfl⟩
    exact qualifyRow_dom a cols raw c hc
  | filter p inner ih =>
    intro r hr c hc
    simp only [eval, List.mem_filter] at hr
    exact ih r hr.1 c hc
  | project items inner _ =>
    intro r hr c hc
    simp only [eval, List.mem_map] at hr
    rcases hr with ⟨r0, _, rfl⟩
    exact evalProjItems_dom items r0 c hc
  | innerJoin l r cond ihl ihr =>
    intro row hr c hc
    simp only [eval, List.mem_flatMap, List.mem_filterMap] at hr
    rcases hr with ⟨rl, hrl, rr, hrr, hcond⟩
    split at hcond
    · cases hcond
      rcases Row.merge_dom hc with hc1 | hc2
      · exact List.mem_append.mpr (Or.inl (ihl rl hrl c hc1))
      · exact List.mem_append.mpr (Or.inr (ihr rr hrr c hc2))
    · cases hcond
  | leftJoin l r cond ihl ihr =>
    intro row hr c hc
    simp only [eval, List.mem_flatMap] at hr
    rcases hr with ⟨rl, hrl, hrow⟩
    split at hrow
    · simp only [List.mem_singleton] at hrow
      subst hrow
      rcases Row.merge_dom hc with hc1 | hc2
      · exact List.mem_append.mpr (Or.inl (ihl rl hrl c hc1))
      · simp only [Row.nullPad] at hc2
        split at hc2
        · rename_i hc_in
          exact List.mem_append.mpr (Or.inr hc_in)
        · cases hc2
    · simp only [List.mem_filterMap] at hrow
      rcases hrow with ⟨rr, hrr, hcond⟩
      split at hcond
      · cases hcond
        rcases Row.merge_dom hc with hc1 | hc2
        · exact List.mem_append.mpr (Or.inl (ihl rl hrl c hc1))
        · exact List.mem_append.mpr (Or.inr (ihr rr hrr c hc2))
      · cases hcond
  | groupBy keys aggs inner _ =>
    intro r hr c hc
    simp only [eval, List.mem_map] at hr
    rcases hr with ⟨k, _, rfl⟩
    simp only [buildGroupRow] at hc
    have hc' := setColsFromPairs_dom _ c hc
    rw [List.map_append] at hc'
    rcases List.mem_append.mp hc' with hkp | hap
    · simp only [queryCols, List.mem_append]
      left
      rcases List.mem_map.mp hkp with ⟨⟨c', v'⟩, hzip, rfl⟩
      exact (List.of_mem_zip hzip).1
    · simp only [queryCols, List.mem_append]
      right
      simpa [List.map_map] using hap
  | unionAll l r ihl ihr =>
    intro row hr c hc
    simp only [eval, List.mem_append] at hr
    simp only [queryCols, List.mem_append, List.mem_filter]
    rcases hr with hl | hr'
    · exact Or.inl (ihl row hl c hc)
    · have hcr := ihr row hr' c hc
      by_cases hcl : c ∈ queryCols l
      · exact Or.inl hcl
      · exact Or.inr ⟨hcr, by simp [hcl]⟩
  | corrAggFilter o _ _ _ _ _ _ iho _ =>
    intro r hr c hc
    simp only [eval, List.mem_filter] at hr
    exact iho r hr.1 c hc

/-! ### eval 合同性補題 (部分木書き換え用) -/

theorem eval_filter_congr (db : DB) (p : Pred) {q1 q2 : Query}
    (h : BagEq (eval db q1) (eval db q2)) :
    BagEq (eval db (.filter p q1)) (eval db (.filter p q2)) :=
  h.filter _

theorem eval_project_congr (db : DB) (items : List ProjItem) {q1 q2 : Query}
    (h : BagEq (eval db q1) (eval db q2)) :
    BagEq (eval db (.project items q1)) (eval db (.project items q2)) :=
  h.map _

theorem eval_innerJoin_left_congr (db : DB) (r : Query) (cond : Pred) {l1 l2 : Query}
    (h : BagEq (eval db l1) (eval db l2)) :
    BagEq (eval db (.innerJoin l1 r cond)) (eval db (.innerJoin l2 r cond)) := by
  simp only [eval]
  exact perm_flatMap _ _ h (fun _ => List.Perm.refl _)

theorem eval_innerJoin_right_congr (db : DB) (l : Query) (cond : Pred) {r1 r2 : Query}
    (h : BagEq (eval db r1) (eval db r2)) :
    BagEq (eval db (.innerJoin l r1 cond)) (eval db (.innerJoin l r2 cond)) := by
  simp only [eval]
  apply perm_flatMap_congr
  intro rl
  exact perm_filterMap _ h

theorem eval_leftJoin_left_congr (db : DB) (r : Query) (cond : Pred) {l1 l2 : Query}
    (h : BagEq (eval db l1) (eval db l2)) :
    BagEq (eval db (.leftJoin l1 r cond)) (eval db (.leftJoin l2 r cond)) := by
  simp only [eval]
  exact perm_flatMap _ _ h (fun _ => List.Perm.refl _)

theorem eval_leftJoin_right_congr (db : DB) (l : Query) (cond : Pred) {r1 r2 : Query}
    (h : BagEq (eval db r1) (eval db r2)) (hcols : queryCols r1 = queryCols r2) :
    BagEq (eval db (.leftJoin l r1 cond)) (eval db (.leftJoin l r2 cond)) := by
  simp only [eval, hcols]
  apply perm_flatMap_congr
  intro rl
  have hm :
      ((eval db r1).filterMap fun rr =>
        let m := Row.merge rl rr
        if (evalPred m cond).isTrue then some m else none).Perm
      ((eval db r2).filterMap fun rr =>
        let m := Row.merge rl rr
        if (evalPred m cond).isTrue then some m else none) :=
    perm_filterMap _ h
  cases hm_empty : ((eval db r1).filterMap fun rr =>
      let m := Row.merge rl rr
      if (evalPred m cond).isTrue then some m else none).isEmpty
  · have hm_empty2 : ((eval db r2).filterMap fun rr =>
        let m := Row.merge rl rr
        if (evalPred m cond).isTrue then some m else none).isEmpty = false := by
      cases h1 : (eval db r1).filterMap fun rr =>
          let m := Row.merge rl rr
          if (evalPred m cond).isTrue then some m else none with
      | nil => simp [h1] at hm_empty
      | cons hd tl =>
        rw [h1] at hm
        have hlen := hm.length_eq
        cases h2 : (eval db r2).filterMap fun rr =>
            let m := Row.merge rl rr
            if (evalPred m cond).isTrue then some m else none with
        | nil => rw [h2] at hlen; simp at hlen
        | cons _ _ => rfl
    simp [hm_empty2, hm]
  · have hm_empty2 : ((eval db r2).filterMap fun rr =>
        let m := Row.merge rl rr
        if (evalPred m cond).isTrue then some m else none).isEmpty = true := by
      cases h1 : (eval db r1).filterMap fun rr =>
          let m := Row.merge rl rr
          if (evalPred m cond).isTrue then some m else none with
      | cons _ _ => simp [h1] at hm_empty
      | nil =>
        rw [h1] at hm
        have hlen := hm.length_eq
        cases h2 : (eval db r2).filterMap fun rr =>
            let m := Row.merge rl rr
            if (evalPred m cond).isTrue then some m else none with
        | nil => rfl
        | cons _ _ => rw [h2] at hlen; simp at hlen
    simp [hm_empty2]

theorem eval_groupBy_congr (db : DB) (keys : List ColName) (aggs : List AggItem) {q1 q2 : Query}
    (h : BagEq (eval db q1) (eval db q2)) :
    BagEq (eval db (.groupBy keys aggs q1)) (eval db (.groupBy keys aggs q2)) := by
  simp only [eval]
  have hks : (dedup ((eval db q1).map (rowKey keys))).Perm
             (dedup ((eval db q2).map (rowKey keys))) :=
    perm_dedup (List.Perm.map (rowKey keys) h)
  have h1 :
      ((dedup ((eval db q1).map (rowKey keys))).map fun k =>
        buildGroupRow keys aggs k ((eval db q1).filter fun r => rowKey keys r == k)).Perm
      ((dedup ((eval db q2).map (rowKey keys))).map fun k =>
        buildGroupRow keys aggs k ((eval db q1).filter fun r => rowKey keys r == k)) :=
    hks.map _
  have h2 :
      ((dedup ((eval db q2).map (rowKey keys))).map fun k =>
        buildGroupRow keys aggs k ((eval db q1).filter fun r => rowKey keys r == k)) =
      ((dedup ((eval db q2).map (rowKey keys))).map fun k =>
        buildGroupRow keys aggs k ((eval db q2).filter fun r => rowKey keys r == k)) := by
    apply List.map_congr_left
    intro k _
    exact buildGroupRow_perm keys aggs k (h.filter _)
  rw [h2] at h1
  exact h1

theorem eval_unionAll_left_congr (db : DB) (r : Query) {l1 l2 : Query}
    (h : BagEq (eval db l1) (eval db l2)) :
    BagEq (eval db (.unionAll l1 r)) (eval db (.unionAll l2 r)) :=
  h.append (List.Perm.refl _)

theorem eval_unionAll_right_congr (db : DB) (l : Query) {r1 r2 : Query}
    (h : BagEq (eval db r1) (eval db r2)) :
    BagEq (eval db (.unionAll l r1)) (eval db (.unionAll l r2)) :=
  (List.Perm.refl _).append h

theorem eval_corrAggFilter_outer_congr (db : DB)
    (outerCmpCol : ColName) (cmp : CmpOp) (inner : Query)
    (outerJoinCol innerJoinCol : ColName) (aggOp : AggOp) {o1 o2 : Query}
    (h : BagEq (eval db o1) (eval db o2)) :
    BagEq (eval db (.corrAggFilter o1 outerCmpCol cmp inner outerJoinCol innerJoinCol aggOp))
          (eval db (.corrAggFilter o2 outerCmpCol cmp inner outerJoinCol innerJoinCol aggOp)) := by
  simp only [eval]
  exact h.filter _

theorem eval_corrAggFilter_inner_congr (db : DB)
    (outer : Query) (outerCmpCol : ColName) (cmp : CmpOp)
    (outerJoinCol innerJoinCol : ColName) (aggOp : AggOp) {i1 i2 : Query}
    (h : BagEq (eval db i1) (eval db i2)) :
    BagEq (eval db (.corrAggFilter outer outerCmpCol cmp i1 outerJoinCol innerJoinCol aggOp))
          (eval db (.corrAggFilter outer outerCmpCol cmp i2 outerJoinCol innerJoinCol aggOp)) := by
  simp only [eval]
  have heq :
      (fun ro =>
        let kv := Row.getVal ro outerJoinCol
        let grp := (eval db i1).filter fun ri =>
          match Row.getVal ri innerJoinCol, kv with
          | .null, _ => false
          | _, .null => false
          | v1, v2 => v1 == v2
        let av := evalAgg aggOp grp
        (evalCmp cmp (Row.getVal ro outerCmpCol) av).isTrue) =
      (fun ro =>
        let kv := Row.getVal ro outerJoinCol
        let grp := (eval db i2).filter fun ri =>
          match Row.getVal ri innerJoinCol, kv with
          | .null, _ => false
          | _, .null => false
          | v1, v2 => v1 == v2
        let av := evalAgg aggOp grp
        (evalCmp cmp (Row.getVal ro outerCmpCol) av).isTrue) := by
    funext ro
    dsimp only
    have hgrp :
        ((eval db i1).filter fun ri =>
          match Row.getVal ri innerJoinCol, Row.getVal ro outerJoinCol with
          | .null, _ => false
          | _, .null => false
          | v1, v2 => v1 == v2).Perm
        ((eval db i2).filter fun ri =>
          match Row.getVal ri innerJoinCol, Row.getVal ro outerJoinCol with
          | .null, _ => false
          | _, .null => false
          | v1, v2 => v1 == v2) :=
      h.filter _
    rw [evalAgg_perm aggOp hgrp]
  rw [heq]

end LeanSqlOpt
