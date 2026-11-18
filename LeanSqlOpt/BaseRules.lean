import LeanSqlOpt.VerifiedRule

namespace LeanSqlOpt

/-- スカラ式に出現するカラム名一覧 -/
def exprCols : Expr → List ColName
  | .col c => [c]
  | .lit _ => []
  | .add e1 e2 => exprCols e1 ++ exprCols e2
  | .mul e1 e2 => exprCols e1 ++ exprCols e2

/-- 述語に出現するカラム名一覧 -/
def predCols : Pred → List ColName
  | .trueLit => []
  | .falseLit => []
  | .eq e1 e2 => exprCols e1 ++ exprCols e2
  | .ne e1 e2 => exprCols e1 ++ exprCols e2
  | .gt e1 e2 => exprCols e1 ++ exprCols e2
  | .lt e1 e2 => exprCols e1 ++ exprCols e2
  | .isNull e => exprCols e
  | .isNotNull e => exprCols e
  | .isDistinctFrom e1 e2 => exprCols e1 ++ exprCols e2
  | .not p => predCols p
  | .notTrue p => predCols p
  | .and p q => predCols p ++ predCols q
  | .or p q => predCols p ++ predCols q

/-! ### 行上の一致から evalExpr / evalPred の一致を導く共通補題 -/

theorem evalExpr_eq_on {r1 r2 : Row} {e : Expr}
    (h : ∀ c ∈ exprCols e, r1 c = r2 c) :
    evalExpr r1 e = evalExpr r2 e := by
  induction e with
  | col c =>
    simp only [evalExpr, Row.getVal]
    rw [h c (by simp [exprCols])]
  | lit _ => rfl
  | add e1 e2 ih1 ih2 =>
    simp only [evalExpr]
    rw [ih1 (fun c hc => h c (by simp [exprCols, hc]))]
    rw [ih2 (fun c hc => h c (by simp [exprCols, hc]))]
  | mul e1 e2 ih1 ih2 =>
    simp only [evalExpr]
    rw [ih1 (fun c hc => h c (by simp [exprCols, hc]))]
    rw [ih2 (fun c hc => h c (by simp [exprCols, hc]))]

theorem evalPred_eq_on {r1 r2 : Row} {p : Pred}
    (h : ∀ c ∈ predCols p, r1 c = r2 c) :
    evalPred r1 p = evalPred r2 p := by
  induction p with
  | trueLit => rfl
  | falseLit => rfl
  | eq e1 e2 =>
    simp only [evalPred]
    rw [evalExpr_eq_on (fun c hc => h c (by simp [predCols, hc]))]
    rw [evalExpr_eq_on (fun c hc => h c (by simp [predCols, hc]))]
  | ne e1 e2 =>
    simp only [evalPred]
    rw [evalExpr_eq_on (fun c hc => h c (by simp [predCols, hc]))]
    rw [evalExpr_eq_on (fun c hc => h c (by simp [predCols, hc]))]
  | gt e1 e2 =>
    simp only [evalPred]
    rw [evalExpr_eq_on (fun c hc => h c (by simp [predCols, hc]))]
    rw [evalExpr_eq_on (fun c hc => h c (by simp [predCols, hc]))]
  | lt e1 e2 =>
    simp only [evalPred]
    rw [evalExpr_eq_on (fun c hc => h c (by simp [predCols, hc]))]
    rw [evalExpr_eq_on (fun c hc => h c (by simp [predCols, hc]))]
  | isNull e =>
    simp only [evalPred]
    rw [evalExpr_eq_on (fun c hc => h c (by simp [predCols, hc]))]
  | isNotNull e =>
    simp only [evalPred]
    rw [evalExpr_eq_on (fun c hc => h c (by simp [predCols, hc]))]
  | isDistinctFrom e1 e2 =>
    simp only [evalPred]
    rw [evalExpr_eq_on (fun c hc => h c (by simp [predCols, hc]))]
    rw [evalExpr_eq_on (fun c hc => h c (by simp [predCols, hc]))]
  | not p ih =>
    simp only [evalPred]
    rw [ih (fun c hc => h c (by simp [predCols, hc]))]
  | notTrue p ih =>
    simp only [evalPred]
    rw [ih (fun c hc => h c (by simp [predCols, hc]))]
  | and p q ihp ihq =>
    simp only [evalPred]
    rw [ihp (fun c hc => h c (by simp [predCols, hc]))]
    rw [ihq (fun c hc => h c (by simp [predCols, hc]))]
  | or p q ihp ihq =>
    simp only [evalPred]
    rw [ihp (fun c hc => h c (by simp [predCols, hc]))]
    rw [ihq (fun c hc => h c (by simp [predCols, hc]))]

theorem Row.merge_eq_left_of_not_right {rl rr : Row} {c : ColName}
    (hnone : rr c = none) :
    Row.merge rl rr c = rl c := by
  simp only [Row.merge]
  cases rl c <;> simp [hnone]

theorem Row.merge_eq_right_of_not_left {rl rr : Row} {c : ColName}
    (hnone : rl c = none) :
    Row.merge rl rr c = rr c := by
  simp only [Row.merge, hnone]

theorem row_none_of_not_in_dom {db : DB} {q : Query} {r : Row} {c : ColName}
    (hr : r ∈ eval db q) (hnot : c ∉ queryCols q) :
    r c = none := by
  cases hrc : r c with
  | none => rfl
  | some v =>
    have hsome : (r c).isSome = true := by simp [hrc]
    exact False.elim (hnot (eval_row_dom db q r hr c hsome))

/-! ### リスト操作補助定理 -/

theorem filter_flatMap {xs : List α} (f : α → List β) (p : β → Bool) :
    (xs.flatMap f).filter p = xs.flatMap (fun x => (f x).filter p) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.flatMap_cons, List.filter_append, ih]

theorem TriBool.isTrue_and (a b : TriBool) :
    (a.and b).isTrue = (a.isTrue && b.isTrue) := by
  cases a <;> cases b <;> rfl

theorem filter_filterMap_const {α β : Type} (xs : List α) (f : α → Option β) (p : β → Bool) (b : Bool)
    (hp : ∀ x ∈ xs, ∀ y, f x = some y → p y = b) :
    (xs.filterMap f).filter p = if b then xs.filterMap f else [] := by
  induction xs with
  | nil =>
    cases b <;> rfl
  | cons x xs ih =>
    have ih' := ih (fun z hz y hy => hp z (List.mem_cons_of_mem x hz) y hy)
    simp only [List.filterMap_cons]
    cases hx : f x with
    | none => exact ih'
    | some y =>
      have hpy := hp x (List.mem_cons_self ..) y hx
      simp only [List.filter_cons, hpy]
      cases b
      · simp at ih' ⊢; exact ih'
      · simp at ih' ⊢; exact ih'

theorem filter_filterMap_lift {α β : Type} (xs : List α) (f : α → Option β) (p1 : β → Bool) (p2 : α → Bool)
    (hp : ∀ x ∈ xs, ∀ y, f x = some y → p1 y = p2 x) :
    (xs.filterMap f).filter p1 = (xs.filter p2).filterMap f := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    have ih' := ih (fun z hz y hy => hp z (List.mem_cons_of_mem x hz) y hy)
    simp only [List.filterMap_cons, List.filter_cons]
    cases hx : f x with
    | none =>
      cases p2 x <;> simp [hx, ih']
    | some y =>
      have hpy := hp x (List.mem_cons_self ..) y hx
      simp only [List.filter_cons, hpy]
      cases h2 : p2 x <;> simp [hx, ih']

/-! ### 基本最適化ルール群 (すべて証明付き) -/

/-- 基本ルール 1: 恒真フィルタ除去 `Filter TRUE q -> q` -/
def removeTrueFilterRule : VerifiedRule where
  name := "base.remove_true_filter"
  step _ q :=
    match q with
    | .filter .trueLit inner => some inner
    | _ => none
  preservesCols schema q q' h := by
    cases q with
    | filter p inner =>
      cases p <;> simp at h
      subst h
      rfl
    | _ => simp at h
  sound schema q q' h db _ := by
    cases q with
    | filter p inner =>
      cases p <;> simp at h
      subst h
      have hft : ∀ xs : List Row, xs.filter (fun _ => true) = xs := by
        intro xs; induction xs with | nil => rfl | cons x xs ih => simp [ih]
      simp [eval, evalPred, TriBool.isTrue, hft]
    | _ => simp at h

private theorem filter_eval_congr {db : DB} {p : Pred} {q1 q2 : Query}
    (h : eval db q1 = eval db q2) :
    eval db (.filter p q1) = eval db (.filter p q2) := by
  simp only [eval, h]

theorem eval_filter_and_split (db : DB) (p1 p2 : Pred) (inner : Query) :
    eval db (.filter (.and p1 p2) inner) = eval db (.filter p2 (.filter p1 inner)) := by
  simp only [eval, List.filter_filter]
  have hpred : (fun r => (evalPred r (.and p1 p2)).isTrue) =
               (fun r => (evalPred r p2).isTrue && (evalPred r p1).isTrue) := by
    funext r
    simp [evalPred, TriBool.isTrue_and, Bool.and_comm]
  rw [hpred]

theorem eval_filter_and_split_comm (db : DB) (p1 p2 : Pred) (inner : Query) :
    eval db (.filter (.and p1 p2) inner) = eval db (.filter p1 (.filter p2 inner)) := by
  simp only [eval, List.filter_filter]
  have hpred : (fun r => (evalPred r (.and p1 p2)).isTrue) =
               (fun r => (evalPred r p1).isTrue && (evalPred r p2).isTrue) := by
    funext r
    simp [evalPred, TriBool.isTrue_and]
  rw [hpred]

theorem eval_filter_join_left (db : DB) (p : Pred) (l r : Query) (cond : Pred)
    (hall : ∀ c ∈ predCols p, c ∉ queryCols r) :
    eval db (.innerJoin (.filter p l) r cond) = eval db (.filter p (.innerJoin l r cond)) := by
  simp only [eval, filter_flatMap]
  have hpred_eq : ∀ rl, ∀ rr ∈ eval db r,
      ∀ m, (if (evalPred (Row.merge rl rr) cond).isTrue then some (Row.merge rl rr) else none) = some m →
      (evalPred m p).isTrue = (evalPred rl p).isTrue := by
    intro rl rr hrr m hm
    split at hm
    · cases hm
      congr 1
      apply evalPred_eq_on
      intro c hc
      exact Row.merge_eq_left_of_not_right (row_none_of_not_in_dom hrr (hall c hc))
    · cases hm
  have hpiece : ∀ rl,
      ((eval db r).filterMap fun rr =>
        let m := Row.merge rl rr
        if (evalPred m cond).isTrue then some m else none).filter (fun m => (evalPred m p).isTrue) =
      if (evalPred rl p).isTrue then
        (eval db r).filterMap fun rr =>
          let m := Row.merge rl rr
          if (evalPred m cond).isTrue then some m else none
      else [] := fun rl => filter_filterMap_const (eval db r) _ _ _ (hpred_eq rl)
  have hflat : ∀ (ls : List Row),
      (ls.flatMap fun rl =>
        ((eval db r).filterMap fun rr =>
          let m := Row.merge rl rr
          if (evalPred m cond).isTrue then some m else none).filter fun m =>
          (evalPred m p).isTrue) =
      ((ls.filter fun rl => (evalPred rl p).isTrue).flatMap fun rl =>
        (eval db r).filterMap fun rr =>
          let m := Row.merge rl rr
          if (evalPred m cond).isTrue then some m else none) := by
    intro ls
    induction ls with
    | nil => rfl
    | cons rl rls ih =>
      simp only [List.flatMap_cons, List.filter_cons, hpiece rl, ih]
      cases (evalPred rl p).isTrue <;> simp
  rw [hflat (eval db l)]

theorem eval_filter_join_right (db : DB) (p : Pred) (l r : Query) (cond : Pred)
    (hall : ∀ c ∈ predCols p, c ∉ queryCols l) :
    eval db (.innerJoin l (.filter p r) cond) = eval db (.filter p (.innerJoin l r cond)) := by
  simp only [eval, filter_flatMap]
  have hcongr : ∀ rl ∈ eval db l,
      ((eval db r).filterMap fun rr =>
        let m := Row.merge rl rr
        if (evalPred m cond).isTrue then some m else none).filter (fun m => (evalPred m p).isTrue) =
      ((eval db r).filter fun rr => (evalPred rr p).isTrue).filterMap fun rr =>
        let m := Row.merge rl rr
        if (evalPred m cond).isTrue then some m else none := by
    intro rl hrl
    apply filter_filterMap_lift
    intro rr _ m hm
    dsimp only at hm
    split at hm
    · cases hm
      congr 1
      apply evalPred_eq_on
      intro c hc
      exact Row.merge_eq_right_of_not_left (row_none_of_not_in_dom hrl (hall c hc))
    · cases hm
  have hflat : ∀ (ls : List Row), (∀ rl ∈ ls, rl ∈ eval db l) →
      (ls.flatMap fun rl =>
        ((eval db r).filterMap fun rr =>
          let m := Row.merge rl rr
          if (evalPred m cond).isTrue then some m else none).filter fun m =>
          (evalPred m p).isTrue) =
      (ls.flatMap fun rl =>
        ((eval db r).filter fun rr => (evalPred rr p).isTrue).filterMap fun rr =>
          let m := Row.merge rl rr
          if (evalPred m cond).isTrue then some m else none) := by
    intro ls hls
    induction ls with
    | nil => rfl
    | cons rl rls ih =>
      simp only [List.flatMap_cons]
      rw [hcongr rl (hls rl (List.mem_cons_self ..))]
      rw [ih (fun x hx => hls x (List.mem_cons_of_mem rl hx))]
  rw [hflat (eval db l) (fun _ hx => hx)]

/-- 基本ルール 2: 二重フィルタ統合 `Filter p (Filter q r) -> Filter (p AND q) r` -/
def filterMergeRule : VerifiedRule where
  name := "base.filter_merge"
  step _ q :=
    match q with
    | .filter p1 (.filter p2 inner) => some (.filter (.and p1 p2) inner)
    | _ => none
  preservesCols schema q q' h := by
    cases q with
    | filter p1 sub =>
      cases sub <;> simp at h
      subst h
      rfl
    | _ => simp at h
  sound schema q q' h db _ := by
    cases q with
    | filter p1 sub =>
      cases sub with
      | filter p2 inner =>
        simp at h
        subst h
        rw [eval_filter_and_split_comm]
      | _ => simp at h
    | _ => simp at h

/-- 基本ルール 3: フィルタの InnerJoin 左辺プッシュダウン -/
def pushFilterJoinLeftRule : VerifiedRule where
  name := "base.push_filter_join_left"
  step _ q :=
    match q with
    | .filter p (.innerJoin l r cond) =>
      if (predCols p).all (fun c => !(c ∈ queryCols r)) then
        some (.innerJoin (.filter p l) r cond)
      else
        none
    | _ => none
  preservesCols schema q q' h := by
    cases q with
    | filter p sub =>
      cases sub with
      | innerJoin l r cond =>
        simp at h
        rcases h with ⟨_, rfl⟩
        rfl
      | _ => simp at h
    | _ => simp at h
  sound schema q q' h db _ := by
    cases q with
    | filter p sub =>
      cases sub with
      | innerJoin l r cond =>
        simp at h
        rcases h with ⟨hall, rfl⟩
        rw [eval_filter_join_left db p l r cond hall]
      | _ => simp at h
    | _ => simp at h

/-- 基本ルール 4: フィルタの InnerJoin 右辺プッシュダウン -/
def pushFilterJoinRightRule : VerifiedRule where
  name := "base.push_filter_join_right"
  step _ q :=
    match q with
    | .filter p (.innerJoin l r cond) =>
      if (predCols p).all (fun c => !(c ∈ queryCols l)) then
        some (.innerJoin l (.filter p r) cond)
      else
        none
    | _ => none
  preservesCols schema q q' h := by
    cases q with
    | filter p sub =>
      cases sub with
      | innerJoin l r cond =>
        simp at h
        rcases h with ⟨_, rfl⟩
        rfl
      | _ => simp at h
    | _ => simp at h
  sound schema q q' h db _ := by
    cases q with
    | filter p sub =>
      cases sub with
      | innerJoin l r cond =>
        simp at h
        rcases h with ⟨hall, rfl⟩
        rw [eval_filter_join_right db p l r cond hall]
      | _ => simp at h
    | _ => simp at h

/-- 基本ルール 5: AND フィルタ片側の InnerJoin 左辺プッシュダウン -/
def pushFilterAndJoinLeftRule : VerifiedRule where
  name := "base.push_filter_and_join_left"
  step _ q :=
    match q with
    | .filter (.and p1 p2) (.innerJoin l r cond) =>
      if (predCols p1).all (fun c => !(c ∈ queryCols r)) then
        some (.filter p2 (.innerJoin (.filter p1 l) r cond))
      else if (predCols p2).all (fun c => !(c ∈ queryCols r)) then
        some (.filter p1 (.innerJoin (.filter p2 l) r cond))
      else
        none
    | _ => none
  preservesCols schema q q' h := by
    cases q with
    | filter p sub =>
      cases p with
      | and p1 p2 =>
        cases sub with
        | innerJoin l r cond =>
          dsimp only at h
          split at h
          · cases h; rfl
          · split at h
            · cases h; rfl
            · cases h
        | _ => simp at h
      | _ => simp at h
    | _ => simp at h
  sound schema q q' h db _ := by
    cases q with
    | filter p sub =>
      cases p with
      | and p1 p2 =>
        cases sub with
        | innerJoin l r cond =>
          dsimp only at h
          split at h
          · rename_i h1
            cases h
            simp at h1
            rw [filter_eval_congr (eval_filter_join_left db p1 l r cond h1), ← eval_filter_and_split]
          · split at h
            · rename_i h2
              cases h
              simp at h2
              rw [filter_eval_congr (eval_filter_join_left db p2 l r cond h2), ← eval_filter_and_split_comm]
            · cases h
        | _ => simp at h
      | _ => simp at h
    | _ => simp at h

/-- 基本ルール 6: AND フィルタ片側の InnerJoin 右辺プッシュダウン -/
def pushFilterAndJoinRightRule : VerifiedRule where
  name := "base.push_filter_and_join_right"
  step _ q :=
    match q with
    | .filter (.and p1 p2) (.innerJoin l r cond) =>
      if (predCols p1).all (fun c => !(c ∈ queryCols l)) then
        some (.filter p2 (.innerJoin l (.filter p1 r) cond))
      else if (predCols p2).all (fun c => !(c ∈ queryCols l)) then
        some (.filter p1 (.innerJoin l (.filter p2 r) cond))
      else
        none
    | _ => none
  preservesCols schema q q' h := by
    cases q with
    | filter p sub =>
      cases p with
      | and p1 p2 =>
        cases sub with
        | innerJoin l r cond =>
          dsimp only at h
          split at h
          · cases h; rfl
          · split at h
            · cases h; rfl
            · cases h
        | _ => simp at h
      | _ => simp at h
    | _ => simp at h
  sound schema q q' h db _ := by
    cases q with
    | filter p sub =>
      cases p with
      | and p1 p2 =>
        cases sub with
        | innerJoin l r cond =>
          dsimp only at h
          split at h
          · rename_i h1
            cases h
            simp at h1
            rw [filter_eval_congr (eval_filter_join_right db p1 l r cond h1), ← eval_filter_and_split]
          · split at h
            · rename_i h2
              cases h
              simp at h2
              rw [filter_eval_congr (eval_filter_join_right db p2 l r cond h2), ← eval_filter_and_split_comm]
            · cases h
        | _ => simp at h
      | _ => simp at h
    | _ => simp at h

def baseRules : List VerifiedRule :=
  [ removeTrueFilterRule
  , pushFilterJoinLeftRule
  , pushFilterJoinRightRule
  , pushFilterAndJoinLeftRule
  , pushFilterAndJoinRightRule
  , filterMergeRule
  ]

end LeanSqlOpt
