import LeanSqlOpt.Semantics

namespace LeanSqlOpt

/-- 証明付き最適化ルール:
    書き換え関数 `step` とともに、カラム保存性 (`preservesCols`) と
    Bag意味論における健全性証明 (`sound`) を型として必須化する。 -/
structure VerifiedRule where
  name : String
  step : Schema → Query → Option Query
  preservesCols : ∀ schema q q', step schema q = some q' → queryCols q' = queryCols q
  sound : ∀ schema q q', step schema q = some q' →
    ∀ db, ValidDB schema db → BagEq (eval db q') (eval db q)

/-- ルールのリストから最初に適用可能なものを1回試す -/
def tryRules (schema : Schema) (rules : List VerifiedRule) (q : Query) : Option (Query × String) :=
  match rules with
  | [] => none
  | r :: rs =>
    match r.step schema q with
    | some q' => some (q', r.name)
    | none => tryRules schema rs q

theorem tryRules_sound (schema : Schema) (rules : List VerifiedRule) (q q' : Query) (rname : String)
    (h : tryRules schema rules q = some (q', rname)) :
    queryCols q' = queryCols q ∧ ∀ db, ValidDB schema db → BagEq (eval db q') (eval db q) := by
  induction rules with
  | nil => simp [tryRules] at h
  | cons r rs ih =>
    simp only [tryRules] at h
    cases hstep : r.step schema q with
    | some q0 =>
      rw [hstep] at h
      cases h
      exact ⟨r.preservesCols schema q q' hstep, r.sound schema q q' hstep⟩
    | none =>
      rw [hstep] at h
      exact ih h

/-- クエリASTのトップダウン1ステップ書き換え（ルートで試み、不発なら子を再帰的に1箇所書き換える） -/
def rewriteOneStep (schema : Schema) (rules : List VerifiedRule) (q : Query) : Option (Query × String) :=
  match tryRules schema rules q with
  | some res => some res
  | none =>
    match q with
    | .scan _ _ _ => none
    | .filter p inner =>
      match rewriteOneStep schema rules inner with
      | some (inner', rn) => some (.filter p inner', rn)
      | none => none
    | .project items inner =>
      match rewriteOneStep schema rules inner with
      | some (inner', rn) => some (.project items inner', rn)
      | none => none
    | .innerJoin l r cond =>
      match rewriteOneStep schema rules l with
      | some (l', rn) => some (.innerJoin l' r cond, rn)
      | none =>
        match rewriteOneStep schema rules r with
        | some (r', rn) => some (.innerJoin l r' cond, rn)
        | none => none
    | .leftJoin l r cond =>
      match rewriteOneStep schema rules l with
      | some (l', rn) => some (.leftJoin l' r cond, rn)
      | none =>
        match rewriteOneStep schema rules r with
        | some (r', rn) => some (.leftJoin l r' cond, rn)
        | none => none
    | .groupBy keys aggs inner =>
      match rewriteOneStep schema rules inner with
      | some (inner', rn) => some (.groupBy keys aggs inner', rn)
      | none => none
    | .unionAll l r =>
      match rewriteOneStep schema rules l with
      | some (l', rn) => some (.unionAll l' r, rn)
      | none =>
        match rewriteOneStep schema rules r with
        | some (r', rn) => some (.unionAll l r', rn)
        | none => none
    | .corrAggFilter o oc cmp i ojc ijc op =>
      match rewriteOneStep schema rules o with
      | some (o', rn) => some (.corrAggFilter o' oc cmp i ojc ijc op, rn)
      | none =>
        match rewriteOneStep schema rules i with
        | some (i', rn) => some (.corrAggFilter o oc cmp i' ojc ijc op, rn)
        | none => none

theorem rewriteOneStep_sound (schema : Schema) (rules : List VerifiedRule)
    (q q' : Query) (rn : String)
    (h : rewriteOneStep schema rules q = some (q', rn)) :
    queryCols q' = queryCols q ∧ ∀ db, ValidDB schema db → BagEq (eval db q') (eval db q) := by
  induction q generalizing q' rn with
  | scan t a cols =>
    unfold rewriteOneStep at h
    cases htr : tryRules schema rules (.scan t a cols) with
    | some res =>
      rw [htr] at h; cases h
      exact tryRules_sound schema rules (.scan t a cols) q' rn htr
    | none =>
      rw [htr] at h; simp at h
  | filter p inner ih =>
    unfold rewriteOneStep at h
    cases htr : tryRules schema rules (.filter p inner) with
    | some res =>
      rw [htr] at h; cases h
      exact tryRules_sound schema rules (.filter p inner) q' rn htr
    | none =>
      rw [htr] at h
      dsimp only at h
      cases hrec : rewriteOneStep schema rules inner with
      | none => rw [hrec] at h; simp at h
      | some res =>
        rw [hrec] at h
        rcases res with ⟨inner', rn'⟩
        cases h
        rcases ih inner' rn hrec with ⟨hc, hs⟩
        exact ⟨hc, fun db hdb => eval_filter_congr db p (hs db hdb)⟩
  | project items inner ih =>
    unfold rewriteOneStep at h
    cases htr : tryRules schema rules (.project items inner) with
    | some res =>
      rw [htr] at h; cases h
      exact tryRules_sound schema rules (.project items inner) q' rn htr
    | none =>
      rw [htr] at h
      dsimp only at h
      cases hrec : rewriteOneStep schema rules inner with
      | none => rw [hrec] at h; simp at h
      | some res =>
        rw [hrec] at h
        rcases res with ⟨inner', rn'⟩
        cases h
        rcases ih inner' rn hrec with ⟨_, hs⟩
        exact ⟨rfl, fun db hdb => eval_project_congr db items (hs db hdb)⟩
  | innerJoin l r cond ihl ihr =>
    unfold rewriteOneStep at h
    cases htr : tryRules schema rules (.innerJoin l r cond) with
    | some res =>
      rw [htr] at h; cases h
      exact tryRules_sound schema rules (.innerJoin l r cond) q' rn htr
    | none =>
      rw [htr] at h
      dsimp only at h
      cases hrecl : rewriteOneStep schema rules l with
      | some res =>
        rw [hrecl] at h
        rcases res with ⟨l', rn'⟩
        cases h
        rcases ihl l' rn hrecl with ⟨hc, hs⟩
        exact ⟨by simp [queryCols, hc], fun db hdb => eval_innerJoin_left_congr db r cond (hs db hdb)⟩
      | none =>
        rw [hrecl] at h
        dsimp only at h
        cases hrecr : rewriteOneStep schema rules r with
        | none => rw [hrecr] at h; simp at h
        | some res =>
          rw [hrecr] at h
          rcases res with ⟨r', rn'⟩
          cases h
          rcases ihr r' rn hrecr with ⟨hc, hs⟩
          exact ⟨by simp [queryCols, hc], fun db hdb => eval_innerJoin_right_congr db l cond (hs db hdb)⟩
  | leftJoin l r cond ihl ihr =>
    unfold rewriteOneStep at h
    cases htr : tryRules schema rules (.leftJoin l r cond) with
    | some res =>
      rw [htr] at h; cases h
      exact tryRules_sound schema rules (.leftJoin l r cond) q' rn htr
    | none =>
      rw [htr] at h
      dsimp only at h
      cases hrecl : rewriteOneStep schema rules l with
      | some res =>
        rw [hrecl] at h
        rcases res with ⟨l', rn'⟩
        cases h
        rcases ihl l' rn hrecl with ⟨hc, hs⟩
        exact ⟨by simp [queryCols, hc], fun db hdb => eval_leftJoin_left_congr db r cond (hs db hdb)⟩
      | none =>
        rw [hrecl] at h
        dsimp only at h
        cases hrecr : rewriteOneStep schema rules r with
        | none => rw [hrecr] at h; simp at h
        | some res =>
          rw [hrecr] at h
          rcases res with ⟨r', rn'⟩
          cases h
          rcases ihr r' rn hrecr with ⟨hc, hs⟩
          exact ⟨by simp [queryCols, hc], fun db hdb => eval_leftJoin_right_congr db l cond (hs db hdb) hc⟩
  | groupBy keys aggs inner ih =>
    unfold rewriteOneStep at h
    cases htr : tryRules schema rules (.groupBy keys aggs inner) with
    | some res =>
      rw [htr] at h; cases h
      exact tryRules_sound schema rules (.groupBy keys aggs inner) q' rn htr
    | none =>
      rw [htr] at h
      dsimp only at h
      cases hrec : rewriteOneStep schema rules inner with
      | none => rw [hrec] at h; simp at h
      | some res =>
        rw [hrec] at h
        rcases res with ⟨inner', rn'⟩
        cases h
        rcases ih inner' rn hrec with ⟨_, hs⟩
        exact ⟨rfl, fun db hdb => eval_groupBy_congr db keys aggs (hs db hdb)⟩
  | unionAll l r ihl ihr =>
    unfold rewriteOneStep at h
    cases htr : tryRules schema rules (.unionAll l r) with
    | some res =>
      rw [htr] at h; cases h
      exact tryRules_sound schema rules (.unionAll l r) q' rn htr
    | none =>
      rw [htr] at h
      dsimp only at h
      cases hrecl : rewriteOneStep schema rules l with
      | some res =>
        rw [hrecl] at h
        rcases res with ⟨l', rn'⟩
        cases h
        rcases ihl l' rn hrecl with ⟨hc, hs⟩
        exact ⟨by simp [queryCols, hc], fun db hdb => eval_unionAll_left_congr db r (hs db hdb)⟩
      | none =>
        rw [hrecl] at h
        dsimp only at h
        cases hrecr : rewriteOneStep schema rules r with
        | none => rw [hrecr] at h; simp at h
        | some res =>
          rw [hrecr] at h
          rcases res with ⟨r', rn'⟩
          cases h
          rcases ihr r' rn hrecr with ⟨hc, hs⟩
          exact ⟨by simp [queryCols, hc], fun db hdb => eval_unionAll_right_congr db l (hs db hdb)⟩
  | corrAggFilter o oc cmp i ojc ijc op iho ihi =>
    unfold rewriteOneStep at h
    cases htr : tryRules schema rules (.corrAggFilter o oc cmp i ojc ijc op) with
    | some res =>
      rw [htr] at h; cases h
      exact tryRules_sound schema rules (.corrAggFilter o oc cmp i ojc ijc op) q' rn htr
    | none =>
      rw [htr] at h
      dsimp only at h
      cases hreco : rewriteOneStep schema rules o with
      | some res =>
        rw [hreco] at h
        rcases res with ⟨o', rn'⟩
        cases h
        rcases iho o' rn hreco with ⟨hc, hs⟩
        exact ⟨hc, fun db hdb => eval_corrAggFilter_outer_congr db oc cmp i ojc ijc op (hs db hdb)⟩
      | none =>
        rw [hreco] at h
        dsimp only at h
        cases hreci : rewriteOneStep schema rules i with
        | none => rw [hreci] at h; simp at h
        | some res =>
          rw [hreci] at h
          rcases res with ⟨i', rn'⟩
          cases h
          rcases ihi i' rn hreci with ⟨_, hs⟩
          exact ⟨rfl, fun db hdb => eval_corrAggFilter_inner_congr db o oc cmp ojc ijc op (hs db hdb)⟩

/-- 最大 fuel 回まで証明付きルールを繰り返して適用するオプティマイザ本体 -/
def optimizeWithLog (fuel : Nat) (schema : Schema) (rules : List VerifiedRule) (q : Query) :
    Query × List String :=
  match fuel with
  | 0 => (q, [])
  | n + 1 =>
    match rewriteOneStep schema rules q with
    | some (q', rn) =>
      let (qFinal, log) := optimizeWithLog n schema rules q'
      (qFinal, rn :: log)
    | none => (q, [])

/-- オプティマイザ全体の健全性定理:
    任意の fuel, スキーマ, 証明付きルール列, クエリに対し、
    最適化前後のクエリは ValidDB の下で Bag 等価である。 -/
theorem optimizeWithLog_sound (fuel : Nat) (schema : Schema) (rules : List VerifiedRule) (q : Query) :
    ∀ db, ValidDB schema db →
      BagEq (eval db (optimizeWithLog fuel schema rules q).1) (eval db q) := by
  induction fuel generalizing q with
  | zero =>
    intro db _
    exact BagEq.refl _
  | succ n ih =>
    intro db hdb
    simp only [optimizeWithLog]
    cases hstep : rewriteOneStep schema rules q with
    | none =>
      exact BagEq.refl _
    | some res =>
      rcases res with ⟨q', rn⟩
      have hs1 := (rewriteOneStep_sound schema rules q q' rn hstep).2 db hdb
      have hs2 := ih q' db hdb
      exact hs2.trans hs1

end LeanSqlOpt
