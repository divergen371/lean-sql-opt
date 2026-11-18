import LeanSqlOpt.BaseRules

namespace LeanSqlOpt

/-! ### 共通補助関数・補題 -/

/-- リストの互いに素チェック -/
def disjointCols (xs ys : List ColName) : Bool :=
  xs.all (fun c => !(c ∈ ys))

theorem disjointCols_iff {xs ys : List ColName} :
    disjointCols xs ys = true ↔ ∀ c ∈ xs, c ∉ ys := by
  simp [disjointCols, List.all_eq_true]

theorem evalProjItems_eq_on {items : List ProjItem} {r1 r2 : Row}
    (h : ∀ it ∈ items, ∀ c ∈ exprCols it.expr, r1 c = r2 c) :
    evalProjItems items r1 = evalProjItems items r2 := by
  induction items with
  | nil => rfl
  | cons it rest ih =>
    funext c
    simp only [evalProjItems]
    have h1 : evalExpr r1 it.expr = evalExpr r2 it.expr :=
      evalExpr_eq_on (h it (List.mem_cons_self ..))
    have h2 : evalProjItems rest r1 c = evalProjItems rest r2 c := by
      have hrest := ih (fun it' hit' => h it' (List.mem_cons_of_mem it hit'))
      rw [hrest]
    simp [h1, h2]

theorem qualCol_inj {a c1 c2 : String} (h : qualCol a c1 = qualCol a c2) : c1 = c2 := by
  simp only [qualCol] at h
  have hchars : (a ++ "__" ++ c1).toList = (a ++ "__" ++ c2).toList := congrArg String.toList h
  simp only [String.toList_append, List.append_assoc] at hchars
  have hc : c1.toList = c2.toList := List.append_cancel_left (List.append_cancel_left hchars)
  exact String.ofList_toList (s := c1) ▸ String.ofList_toList (s := c2) ▸ congrArg String.ofList hc

theorem qualifyRow_apply {a : String} {cols : List ColName} {raw : Row} {c : ColName}
    (hc : c ∈ cols) :
    qualifyRow a cols raw (qualCol a c) = raw c := by
  induction cols with
  | nil => cases hc
  | cons x xs ih =>
    simp only [qualifyRow]
    split
    · rename_i heq
      have hxeq : x = c := qualCol_inj (beq_iff_eq.mp heq).symm
      subst hxeq
      rfl
    · rename_i hne
      rcases List.mem_cons.mp hc with rfl | hmem
      · simp at hne
      · exact ih hmem

/-! ### 追加ルール 1: 3値論理対応・排他分割による OR -> UNION ALL 変換 -/

theorem TriBool.or_split_disjoint (a b : TriBool) :
    (a.isTrue && (b.and a.notTrue).isTrue) = false := by
  cases a <;> cases b <;> rfl

theorem TriBool.or_split_union (a b : TriBool) :
    (a.or b).isTrue = (a.isTrue || (b.and a.notTrue).isTrue) := by
  cases a <;> cases b <;> rfl

theorem filter_disjoint_union_perm {α : Type} (xs : List α) (p1 p2 : α → Bool)
    (hdisj : ∀ x, (p1 x && p2 x) = false) :
    (xs.filter (fun x => p1 x || p2 x)).Perm (xs.filter p1 ++ xs.filter p2) := by
  induction xs with
  | nil => exact List.Perm.nil
  | cons x xs ih =>
    simp only [List.filter_cons]
    have hx := hdisj x
    cases h1 : p1 x <;> cases h2 : p2 x
    · simp only [Bool.false_or, Bool.false_eq_true, if_false]
      exact ih
    · simp only [Bool.false_or, Bool.false_eq_true, if_true, if_false]
      exact (ih.cons x).trans List.perm_middle.symm
    · simp only [Bool.or_false, Bool.false_eq_true, if_true, if_false, List.cons_append]
      exact ih.cons x
    · simp [h1, h2] at hx

/-- 追加ルール 1: `Filter (p OR q) base -> UnionAll (Filter p base) (Filter (q AND NOT_TRUE(p)) base)` -/
def splitOrToUnionAllRule : VerifiedRule where
  name := "perf.split_or_to_union_all"
  step _ q :=
    match q with
    | .filter (.or p1 p2) base =>
      some (.unionAll (.filter p1 base) (.filter (.and p2 (.notTrue p1)) base))
    | _ => none
  preservesCols schema q q' h := by
    cases q with
    | filter p base =>
      cases p with
      | or p1 p2 =>
        simp at h
        subst h
        simp [queryCols, List.filter_eq_nil_iff]
      | _ => simp at h
    | _ => simp at h
  sound schema q q' h db _ := by
    cases q with
    | filter p base =>
      cases p with
      | or p1 p2 =>
        simp at h
        subst h
        change BagEq
          ((eval db base).filter (fun r => (evalPred r p1).isTrue) ++
           (eval db base).filter (fun r => (evalPred r (.and p2 (.notTrue p1))).isTrue))
          ((eval db base).filter (fun r => (evalPred r (.or p1 p2)).isTrue))
        have heq_pred :
            (fun r => (evalPred r (.or p1 p2)).isTrue) =
            (fun r => (evalPred r p1).isTrue || (evalPred r (.and p2 (.notTrue p1))).isTrue) := by
          funext r
          simp only [evalPred, TriBool.or_split_union]
        rw [heq_pred]
        apply List.Perm.symm
        apply filter_disjoint_union_perm
        intro r
        simp only [evalPred, TriBool.or_split_disjoint]
      | _ => simp at h
    | _ => simp at h

/-! ### 追加ルール 2: 外部キー + NOT NULL + UNIQUE による冗長 JOIN 除去 -/

/-- クエリの出力列 `col` がベーステーブルで NOT NULL かつ dstTable.rawDstCol への FK を持つか -/
def colHasNonNullFK (schema : Schema) (q : Query) (col : ColName)
    (dstTable rawDstCol : String) : Bool :=
  match q with
  | .scan t a cols =>
    cols.any fun rc =>
      qualCol a rc == col &&
      schema.notNull t rc &&
      schema.foreignKeys.any (fun fk =>
        fk.srcTable == t && fk.srcCol == rc &&
        fk.dstTable == dstTable && fk.dstCol == rawDstCol)
  | .filter _ inner =>
    colHasNonNullFK schema inner col dstTable rawDstCol
  | .innerJoin l r _ =>
    colHasNonNullFK schema l col dstTable rawDstCol ||
    (disjointCols (queryCols l) (queryCols r) && !(col ∈ queryCols l) &&
      colHasNonNullFK schema r col dstTable rawDstCol)
  | .leftJoin l _ _ =>
    colHasNonNullFK schema l col dstTable rawDstCol
  | _ => false

theorem colHasNonNullFK_sound {schema : Schema} {db : DB} (hdb : ValidDB schema db)
    {q : Query} {col : ColName} {dstTable rawDstCol : String}
    (hfk : colHasNonNullFK schema q col dstTable rawDstCol = true) :
    ∀ r ∈ eval db q, ∃ v : Val, r col = some v ∧ v ≠ .null ∧
      ∃ dr ∈ db dstTable, dr rawDstCol = some v := by
  induction q with
  | scan t a cols =>
    intro r hr
    simp only [colHasNonNullFK, List.any_eq_true, Bool.and_eq_true, beq_iff_eq] at hfk
    rcases hfk with ⟨rc, hrc_mem, ⟨⟨hqual, hnn⟩, fk, hfk_mem, hfk_eq⟩⟩
    rcases hfk_eq with ⟨⟨⟨ht, hsc⟩, hdt⟩, hdc⟩
    subst ht hsc hdt hdc hqual
    simp only [eval, List.mem_map] at hr
    rcases hr with ⟨raw, hraw_mem, rfl⟩
    rcases hdb.notNullHolds fk.srcTable fk.srcCol hnn raw hraw_mem with ⟨v, hv_eq, hv_nn⟩
    rcases hdb.fkHolds fk hfk_mem raw hraw_mem v hv_eq hv_nn with ⟨dr, hdr_mem, hdr_eq⟩
    refine ⟨v, ?_, hv_nn, dr, hdr_mem, hdr_eq⟩
    rw [qualifyRow_apply hrc_mem]
    exact hv_eq
  | filter p inner ih =>
    intro r hr
    simp only [colHasNonNullFK] at hfk
    simp only [eval, List.mem_filter] at hr
    exact ih hfk r hr.1
  | innerJoin l r cond ihl ihr =>
    intro row hr
    simp only [colHasNonNullFK, Bool.or_eq_true, Bool.and_eq_true,
      Bool.not_eq_true', decide_eq_false_iff_not] at hfk
    simp only [eval, List.mem_flatMap, List.mem_filterMap] at hr
    rcases hr with ⟨rl, hrl, rr, hrr, hcond⟩
    split at hcond
    · cases hcond
      rcases hfk with hl | ⟨⟨_, hnotl⟩, hr_fk⟩
      · rcases ihl hl rl hrl with ⟨v, hv_eq, hv_nn, dr, hdr_mem, hdr_eq⟩
        refine ⟨v, ?_, hv_nn, dr, hdr_mem, hdr_eq⟩
        simp [Row.merge, hv_eq]
      · rcases ihr hr_fk rr hrr with ⟨v, hv_eq, hv_nn, dr, hdr_mem, hdr_eq⟩
        refine ⟨v, ?_, hv_nn, dr, hdr_mem, hdr_eq⟩
        rw [Row.merge_eq_right_of_not_left (row_none_of_not_in_dom hrl hnotl)]
        exact hv_eq
    · cases hcond
  | leftJoin l r cond ihl _ =>
    intro row hr
    simp only [colHasNonNullFK] at hfk
    simp only [eval, List.mem_flatMap] at hr
    rcases hr with ⟨rl, hrl, hrow⟩
    rcases ihl hfk rl hrl with ⟨v, hv_eq, hv_nn, dr, hdr_mem, hdr_eq⟩
    split at hrow
    · simp only [List.mem_singleton] at hrow
      subst hrow
      refine ⟨v, ?_, hv_nn, dr, hdr_mem, hdr_eq⟩
      simp [Row.merge, hv_eq]
    · simp only [List.mem_filterMap] at hrow
      rcases hrow with ⟨rr, _, hcond⟩
      split at hcond
      · cases hcond
        refine ⟨v, ?_, hv_nn, dr, hdr_mem, hdr_eq⟩
        simp [Row.merge, hv_eq]
      · cases hcond
  | project _ _ _ => simp [colHasNonNullFK] at hfk
  | groupBy _ _ _ _ => simp [colHasNonNullFK] at hfk
  | unionAll _ _ _ _ => simp [colHasNonNullFK] at hfk
  | corrAggFilter _ _ _ _ _ _ _ _ _ => simp [colHasNonNullFK] at hfk

/-- filterMap で 1 対 1 結合する際の単一結果補題 -/
theorem filterMap_singleton_of_exists_unique {α β : Type} (xs : List α)
    (p : α → Bool) (f : α → β)
    (hex : ∃ x ∈ xs, p x = true)
    (huniq : (xs.filter p).length ≤ 1) :
    ∃ x ∈ xs, p x = true ∧
      xs.filterMap (fun a => if p a then some (f a) else none) = [f x] := by
  induction xs with
  | nil =>
    rcases hex with ⟨x, hx, _⟩
    cases hx
  | cons y ys ih =>
    simp only [List.filter_cons] at huniq
    cases hy : p y
    · simp only [hy, Bool.false_eq_true, if_false] at huniq
      rcases hex with ⟨x, hx_mem, hpx⟩
      rcases List.mem_cons.mp hx_mem with rfl | hx_ys
      · simp [hy] at hpx
      · rcases ih ⟨x, hx_ys, hpx⟩ huniq with ⟨x0, hx0_mem, hpx0, hfm⟩
        refine ⟨x0, List.mem_cons_of_mem y hx0_mem, hpx0, ?_⟩
        simp [hy, hfm]
    · simp only [hy, if_true, List.length_cons] at huniq
      have hzero : (ys.filter p).length = 0 := by omega
      have hnone : ∀ z ∈ ys, p z = false := by
        intro z hz
        cases hz_p : p z
        · rfl
        · have : z ∈ ys.filter p := List.mem_filter.mpr ⟨hz, hz_p⟩
          have hlen_pos : 0 < (ys.filter p).length := List.length_pos_of_mem this
          omega
      have hfm_ys : ys.filterMap (fun a => if p a then some (f a) else none) = [] := by
        clear huniq hzero ih hex
        induction ys with
        | nil => rfl
        | cons z zs ihz =>
          simp only [List.filterMap_cons]
          have hz := hnone z (List.mem_cons_self ..)
          simp only [hz]
          exact ihz (fun w hw => hnone w (List.mem_cons_of_mem z hw))
      refine ⟨y, List.mem_cons_self .., hy, ?_⟩
      simp [hy, hfm_ys]

/-- 右側テーブルへの等価結合条件を正規化して抽出する補助関数 -/
def extractJoinCols (l r : Query) (cond : Pred) : Option (ColName × ColName) :=
  match cond with
  | .eq (.col c1) (.col c2) =>
    if c1 ∈ queryCols l && c2 ∈ queryCols r then some (c1, c2)
    else if c2 ∈ queryCols l && c1 ∈ queryCols r then some (c2, c1)
    else none
  | _ => none

theorem val_beq_comm (v1 v2 : Val) : (v1 == v2) = (v2 == v1) := by
  by_cases h : v1 = v2
  · subst h; rfl
  · have h1 : (v1 == v2) = false := beq_false_of_ne h
    have h2 : (v2 == v1) = false := beq_false_of_ne (Ne.symm h)
    rw [h1, h2]

theorem evalPred_eq_cols_isTrue (r : Row) (c1 c2 : ColName) :
    (evalPred r (.eq (.col c1) (.col c2))).isTrue =
    (match r c1, r c2 with
     | some .null, _ => false
     | _, some .null => false
     | some v1, some v2 => v1 == v2
     | _, _ => false) := by
  simp only [evalPred, evalExpr, Row.getVal]
  cases h1 : r c1 with
  | none =>
    cases h2 : r c2 with
    | none => rfl
    | some v2 => cases v2 <;> rfl
  | some v1 =>
    cases h2 : r c2 with
    | none => cases v1 <;> rfl
    | some v2 =>
      cases v1 with
      | null => cases v2 <;> rfl
      | int a =>
        cases v2 with
        | null => rfl
        | int b =>
          simp only [Option.getD_some]
          by_cases h : a = b <;> simp [h, TriBool.isTrue]
        | str s => rfl
      | str s1 =>
        cases v2 with
        | null => rfl
        | int b => rfl
        | str s2 =>
          simp only [Option.getD_some]
          by_cases h : s1 = s2 <;> simp [h, TriBool.isTrue]

/-- 追加ルール 2: 外部キー + NOT NULL + UNIQUE 制約を用いた冗長 INNER JOIN 除去 -/
def elimRedundantFKJoinRule : VerifiedRule where
  name := "perf.elim_redundant_fk_join"
  step schema q :=
    match q with
    | .project items (.innerJoin l (.scan dstTable dstAlias dstCols) cond) =>
      match extractJoinCols l (.scan dstTable dstAlias dstCols) cond with
      | some (srcCol, dstCol) =>
        let rCols := (dstCols.map (qualCol dstAlias))
        if disjointCols (queryCols l) rCols &&
           (items.all fun it => (exprCols it.expr).all fun c => !(c ∈ rCols)) then
          match dstCols.find? (fun rc => qualCol dstAlias rc == dstCol && schema.uniqueKey dstTable rc) with
          | some rawDstCol =>
            if colHasNonNullFK schema l srcCol dstTable rawDstCol then
              some (.project items l)
            else
              none
          | none => none
        else
          none
      | none => none
    | _ => none
  preservesCols schema q q' h := by
    cases q with
    | project items sub =>
      cases sub with
      | innerJoin l r cond =>
        cases r with
        | scan dstTable dstAlias dstCols =>
          dsimp only at h
          cases hex : extractJoinCols l (.scan dstTable dstAlias dstCols) cond with
          | none => rw [hex] at h; simp at h
          | some p =>
            rw [hex] at h
            dsimp only at h
            split at h
            · cases hfind : dstCols.find? (fun rc => qualCol dstAlias rc == p.2 && schema.uniqueKey dstTable rc) with
              | none => rw [hfind] at h; simp at h
              | some rawDstCol =>
                rw [hfind] at h
                dsimp only at h
                split at h
                · cases h; rfl
                · cases h
            · cases h
        | _ => simp at h
      | _ => simp at h
    | _ => simp at h
  sound schema q q' h db hdb := by
    cases q with
    | project items sub =>
      cases sub with
      | innerJoin l r cond =>
        cases r with
        | scan dstTable dstAlias dstCols =>
          dsimp only at h
          cases hex : extractJoinCols l (.scan dstTable dstAlias dstCols) cond with
          | none => rw [hex] at h; simp at h
          | some pair =>
            rw [hex] at h
            rcases pair with ⟨srcCol, dstCol⟩
            dsimp only at h
            split at h
            · rename_i hchecks
              simp only [Bool.and_eq_true, List.all_eq_true, Bool.not_eq_true',
                decide_eq_false_iff_not] at hchecks
              rcases hchecks with ⟨hdisj, hitems_no_r⟩
              rw [disjointCols_iff] at hdisj
              cases hfind : dstCols.find? (fun rc => qualCol dstAlias rc == dstCol && schema.uniqueKey dstTable rc) with
              | none => rw [hfind] at h; simp at h
              | some rawDstCol =>
                rw [hfind] at h
                dsimp only at h
                split at h
                · rename_i hfk
                  cases h
                  have hraw_mem : rawDstCol ∈ dstCols := List.mem_of_find?_eq_some hfind
                  have hraw_prop := List.find?_some hfind
                  simp only [Bool.and_eq_true, beq_iff_eq] at hraw_prop
                  rcases hraw_prop with ⟨hqual_dst, huniq_dst⟩
                  have hsrc_in_l : srcCol ∈ queryCols l := by
                    simp only [extractJoinCols] at hex
                    cases cond with
                    | eq e1 e2 =>
                      cases e1 <;> cases e2 <;> simp at hex
                      case col.col c1 c2 =>
                        split at hex
                        · cases hex; simp_all
                        · split at hex
                          · cases hex; simp_all
                          · cases hex
                    | _ => simp at hex
                  have hcond_eq : ∀ rl ∈ eval db l, ∀ rr ∈ eval db (.scan dstTable dstAlias dstCols),
                      (evalPred (Row.merge rl rr) cond).isTrue =
                        (match rl srcCol, rr dstCol with
                         | some (.null), _ => false
                         | _, some (.null) => false
                         | some v1, some v2 => v1 == v2
                         | _, _ => false) := by
                    intro rl hrl rr hrr
                    have hsrc_not_r : srcCol ∉ dstCols.map (qualCol dstAlias) := hdisj srcCol hsrc_in_l
                    have hdst_not_l : dstCol ∉ queryCols l := by
                      intro hmem
                      have := hdisj dstCol hmem
                      apply this
                      rw [← hqual_dst]
                      exact List.mem_map.mpr ⟨rawDstCol, hraw_mem, rfl⟩
                    have hm_src : Row.merge rl rr srcCol = rl srcCol :=
                      Row.merge_eq_left_of_not_right (row_none_of_not_in_dom hrr hsrc_not_r)
                    have hm_dst : Row.merge rl rr dstCol = rr dstCol :=
                      Row.merge_eq_right_of_not_left (row_none_of_not_in_dom hrl hdst_not_l)
                    simp only [extractJoinCols] at hex
                    cases cond with
                    | eq e1 e2 =>
                      cases e1 <;> cases e2 <;> simp at hex
                      case col.col c1 c2 =>
                        split at hex
                        · rcases hex with ⟨rfl, rfl⟩
                          rw [evalPred_eq_cols_isTrue, hm_src, hm_dst]
                        · split at hex
                          · rcases hex with ⟨rfl, rfl⟩
                            rw [evalPred_eq_cols_isTrue, hm_src, hm_dst]
                            cases rl srcCol with
                            | none =>
                              cases rr dstCol with
                              | none => rfl
                              | some v2 => cases v2 <;> rfl
                            | some v1 =>
                              cases rr dstCol with
                              | none => cases v1 <;> rfl
                              | some v2 => cases v1 <;> cases v2 <;> simp [val_beq_comm]
                          · cases hex
                    | _ => simp at hex
                  -- 各 rl に対してちょうど1つの rr がマッチすることを示す
                  have hper_rl : ∀ rl ∈ eval db l,
                      (((eval db (.scan dstTable dstAlias dstCols)).filterMap fun rr =>
                        let m := Row.merge rl rr
                        if (evalPred m cond).isTrue then some m else none).map (evalProjItems items)) =
                      [evalProjItems items rl] := by
                    intro rl hrl
                    rcases colHasNonNullFK_sound hdb hfk rl hrl with ⟨v, hv_eq, hv_nn, dr0, hdr0_mem, hdr0_eq⟩
                    have hpred_dr : ∀ dr ∈ db dstTable,
                        (evalPred (Row.merge rl (qualifyRow dstAlias dstCols dr)) cond).isTrue =
                        (dr rawDstCol == some v) := by
                      intro dr hdr
                      have hrr : qualifyRow dstAlias dstCols dr ∈ eval db (.scan dstTable dstAlias dstCols) :=
                        List.mem_map.mpr ⟨dr, hdr, rfl⟩
                      rw [hcond_eq rl hrl _ hrr, hv_eq, ← hqual_dst, qualifyRow_apply hraw_mem]
                      cases hdr_val : dr rawDstCol with
                      | none =>
                        cases v <;> simp
                      | some w =>
                        cases v with
                        | null => exact False.elim (hv_nn rfl)
                        | int a => cases w <;> simp [val_beq_comm]
                        | str s => cases w <;> simp [val_beq_comm]
                    have hex_raw : ∃ dr ∈ db dstTable, (dr rawDstCol == some v) = true :=
                      ⟨dr0, hdr0_mem, beq_iff_eq.mpr hdr0_eq⟩
                    have huniq_raw : ((db dstTable).filter (fun dr => dr rawDstCol == some v)).length ≤ 1 :=
                      hdb.uniqueHolds dstTable rawDstCol huniq_dst v hv_nn
                    rcases filterMap_singleton_of_exists_unique (db dstTable)
                        (fun dr => dr rawDstCol == some v)
                        (fun dr => Row.merge rl (qualifyRow dstAlias dstCols dr))
                        hex_raw huniq_raw with ⟨dr1, hdr1_mem, _, hfm_eq⟩
                    have hfm_eval :
                        ((eval db (.scan dstTable dstAlias dstCols)).filterMap fun rr =>
                          let m := Row.merge rl rr
                          if (evalPred m cond).isTrue then some m else none) =
                        [Row.merge rl (qualifyRow dstAlias dstCols dr1)] := by
                      simp only [eval]
                      have hrewrite :
                          ((db dstTable).map (qualifyRow dstAlias dstCols)).filterMap
                            (fun rr => if (evalPred (Row.merge rl rr) cond).isTrue then some (Row.merge rl rr) else none) =
                          (db dstTable).filterMap
                            (fun dr => if (dr rawDstCol == some v) then some (Row.merge rl (qualifyRow dstAlias dstCols dr)) else none) := by
                        have hgen : ∀ (ds : List Row), (∀ d ∈ ds, d ∈ db dstTable) →
                            (ds.map (qualifyRow dstAlias dstCols)).filterMap
                              (fun rr => if (evalPred (Row.merge rl rr) cond).isTrue then some (Row.merge rl rr) else none) =
                            ds.filterMap
                              (fun dr => if (dr rawDstCol == some v) then some (Row.merge rl (qualifyRow dstAlias dstCols dr)) else none) := by
                          intro ds hds
                          induction ds with
                          | nil => rfl
                          | cons d ds' ih =>
                            simp only [List.map_cons, List.filterMap_cons]
                            have hd := hpred_dr d (hds d (List.mem_cons_self ..))
                            rw [hd]
                            have ih' := ih (fun x hx => hds x (List.mem_cons_of_mem d hx))
                            cases d rawDstCol == some v <;> simp [ih']
                        exact hgen (db dstTable) (fun _ hx => hx)
                      rw [hrewrite]
                      exact hfm_eq
                    rw [hfm_eval]
                    simp only [List.map_cons, List.map_nil]
                    congr 1
                    apply evalProjItems_eq_on
                    intro it hit c hc
                    have hc_not_r : c ∉ dstCols.map (qualCol dstAlias) := hitems_no_r it hit c hc
                    have hrr1 : qualifyRow dstAlias dstCols dr1 ∈ eval db (.scan dstTable dstAlias dstCols) :=
                      List.mem_map.mpr ⟨dr1, hdr1_mem, rfl⟩
                    exact Row.merge_eq_left_of_not_right (row_none_of_not_in_dom hrr1 hc_not_r)
                  -- 全体への結合
                  have hwhole : ∀ (ls : List Row), (∀ rl ∈ ls, rl ∈ eval db l) →
                      (ls.flatMap fun rl =>
                        ((eval db (.scan dstTable dstAlias dstCols)).filterMap fun rr =>
                          let m := Row.merge rl rr
                          if (evalPred m cond).isTrue then some m else none).map (evalProjItems items)) =
                      ls.map (evalProjItems items) := by
                    intro ls hls
                    induction ls with
                    | nil => rfl
                    | cons rl rls ih =>
                      simp only [List.flatMap_cons, List.map_cons]
                      rw [hper_rl rl (hls rl (List.mem_cons_self ..))]
                      rw [ih (fun x hx => hls x (List.mem_cons_of_mem rl hx))]
                      rfl
                  change BagEq (List.map (evalProjItems items) (eval db l))
                    (List.map (evalProjItems items) (eval db (.innerJoin l (.scan dstTable dstAlias dstCols) cond)))
                  rw [show eval db (.innerJoin l (.scan dstTable dstAlias dstCols) cond) =
                    (eval db l).flatMap (fun rl =>
                      (eval db (.scan dstTable dstAlias dstCols)).filterMap fun rr =>
                        let m := Row.merge rl rr
                        if (evalPred m cond).isTrue then some m else none) from rfl]
                  rw [List.map_flatMap]
                  rw [hwhole (eval db l) (fun _ hx => hx)]
                · cases h
            · cases h
        | _ => simp at h
      | _ => simp at h
    | _ => simp at h

/-! ### 追加ルール 3: 相関集約サブクエリのデコレレーション (Subquery Decorrelation) -/

/-- 空集合に対して NULL を返す集約演算子かどうか (COUNT は 0 を返すため false) -/
def isNullOnEmpty : AggOp → Bool
  | .sumCol _ => true
  | .avgCol _ => true
  | .minCol _ => true
  | .maxCol _ => true
  | .countStar => false
  | .countCol _ => false

theorem evalAgg_nil_of_isNullOnEmpty {op : AggOp} (h : isNullOnEmpty op = true) :
    evalAgg op [] = .null := by
  cases op <;> simp [isNullOnEmpty, evalAgg, sumNonNullInts, countNonNull, minNonNullInt, maxNonNullInt] at h ⊢

def cmpToPred (cmp : CmpOp) (e1 e2 : Expr) : Pred :=
  match cmp with
  | .gt => .gt e1 e2
  | .lt => .lt e1 e2
  | .eq => .eq e1 e2

theorem evalCmp_eq_pred (r : Row) (cmp : CmpOp) (c1 c2 : ColName) :
    evalCmp cmp (Row.getVal r c1) (Row.getVal r c2) =
    evalPred r (cmpToPred cmp (.col c1) (.col c2)) := by
  cases cmp <;> simp only [evalCmp, cmpToPred, evalPred, evalExpr] <;>
    cases Row.getVal r c1 <;> cases Row.getVal r c2 <;> simp

theorem evalCmp_null_right (cmp : CmpOp) (v : Val) :
    (evalCmp cmp v .null).isTrue = false := by
  cases v <;> cases cmp <;> rfl

/-- クエリがスキーマに定義された列のみを scan し、unionAll の列も一致するかのチェック -/
def allColsDefined (schema : Schema) : Query → Bool
  | .scan t _ cols => cols.all (fun c => c ∈ schema.tableCols t)
  | .filter _ q => allColsDefined schema q
  | .project _ q => allColsDefined schema q
  | .innerJoin l r _ => allColsDefined schema l && allColsDefined schema r
  | .leftJoin l r _ => allColsDefined schema l && allColsDefined schema r
  | .groupBy _ _ q => allColsDefined schema q
  | .unionAll l r =>
    allColsDefined schema l && allColsDefined schema r &&
    (queryCols r).all (fun c => c ∈ queryCols l) &&
    (queryCols l).all (fun c => c ∈ queryCols r)
  | .corrAggFilter o _ _ i _ _ _ => allColsDefined schema o && allColsDefined schema i

theorem qualifyRow_isSome {a : String} {cols : List ColName} {raw : Row} {c : ColName}
    (hmem : c ∈ cols.map (qualCol a))
    (hraw : ∀ rc ∈ cols, (raw rc).isSome = true) :
    (qualifyRow a cols raw c).isSome = true := by
  induction cols with
  | nil => simp at hmem
  | cons x xs ih =>
    simp only [List.map_cons, List.mem_cons] at hmem
    simp only [qualifyRow]
    split
    · exact hraw x (List.mem_cons_self ..)
    · rename_i hne
      rcases hmem with rfl | hmem_xs
      · simp at hne
      · exact ih hmem_xs (fun rc hrc => hraw rc (List.mem_cons_of_mem x hrc))

theorem mem_map_fst_zip {α β : Type} (ks : List α) (vs : List β) (h : ks.length = vs.length)
    {x : α} (hx : x ∈ ks) :
    x ∈ (ks.zip vs).map Prod.fst := by
  induction ks generalizing vs with
  | nil => simp at hx
  | cons k ks' ih =>
    cases vs with
    | nil => simp at h
    | cons v vs' =>
      simp only [List.length_cons] at h
      simp only [List.zip_cons_cons, List.map_cons, List.mem_cons] at hx ⊢
      rcases hx with rfl | hx'
      · exact Or.inl rfl
      · exact Or.inr (ih vs' (by omega) hx')

theorem setColsFromPairs_isSome {pairs : List (ColName × Val)} {c : ColName}
    (hc : c ∈ pairs.map Prod.fst) :
    (setColsFromPairs pairs c).isSome = true := by
  induction pairs with
  | nil => simp at hc
  | cons p ps ih =>
    rcases p with ⟨k, v⟩
    simp only [List.map_cons, List.mem_cons] at hc
    simp only [setColsFromPairs]
    split
    · rfl
    · rename_i hne
      rcases hc with rfl | hc'
      · simp at hne
      · exact ih hc'

theorem evalProjItems_isSome {items : List ProjItem} {r : Row} {c : ColName}
    (hc : c ∈ items.map (·.alias)) :
    (evalProjItems items r c).isSome = true := by
  induction items with
  | nil => simp at hc
  | cons it rest ih =>
    simp only [List.map_cons, List.mem_cons] at hc
    simp only [evalProjItems]
    split
    · rfl
    · rename_i hne
      rcases hc with rfl | hc'
      · simp at hne
      · exact ih hc'

theorem allColsDefined_sound {schema : Schema} {db : DB} (hdb : ValidDB schema db)
    {q : Query} (hdef : allColsDefined schema q = true) :
    ∀ r ∈ eval db q, ∀ c ∈ queryCols q, (r c).isSome = true := by
  induction q with
  | scan t a cols =>
    intro r hr c hc
    simp only [allColsDefined, List.all_eq_true, decide_eq_true_eq] at hdef
    simp only [eval, List.mem_map] at hr
    rcases hr with ⟨raw, hraw_mem, rfl⟩
    apply qualifyRow_isSome hc
    intro rc hrc
    exact (hdb.colsMatch t raw hraw_mem rc).mpr (hdef rc hrc)
  | filter p inner ih =>
    intro r hr c hc
    simp only [allColsDefined] at hdef
    simp only [eval, List.mem_filter] at hr
    exact ih hdef r hr.1 c hc
  | project items inner _ =>
    intro r hr c hc
    simp only [eval, List.mem_map] at hr
    rcases hr with ⟨r0, _, rfl⟩
    exact evalProjItems_isSome hc
  | innerJoin l r cond ihl ihr =>
    intro row hr c hc
    simp only [allColsDefined, Bool.and_eq_true] at hdef
    simp only [eval, List.mem_flatMap, List.mem_filterMap] at hr
    simp only [queryCols, List.mem_append] at hc
    rcases hr with ⟨rl, hrl, rr, hrr, hcond⟩
    split at hcond
    · cases hcond
      rcases hc with hcl | hcr
      · have h1 := ihl hdef.1 rl hrl c hcl
        cases hrlc : rl c with
        | none => simp [hrlc] at h1
        | some v => simp [Row.merge, hrlc]
      · have h2 := ihr hdef.2 rr hrr c hcr
        simp only [Row.merge]
        cases rl c with
        | some _ => rfl
        | none => exact h2
    · cases hcond
  | leftJoin l r cond ihl ihr =>
    intro row hr c hc
    simp only [allColsDefined, Bool.and_eq_true] at hdef
    simp only [eval, List.mem_flatMap] at hr
    simp only [queryCols, List.mem_append] at hc
    rcases hr with ⟨rl, hrl, hrow⟩
    split at hrow
    · simp only [List.mem_singleton] at hrow
      subst hrow
      rcases hc with hcl | hcr
      · have h1 := ihl hdef.1 rl hrl c hcl
        cases hrlc : rl c with
        | none => simp [hrlc] at h1
        | some _ => simp [Row.merge, hrlc]
      · simp only [Row.merge]
        cases rl c with
        | some _ => rfl
        | none => simp [Row.nullPad, hcr]
    · simp only [List.mem_filterMap] at hrow
      rcases hrow with ⟨rr, hrr, hcond⟩
      split at hcond
      · cases hcond
        rcases hc with hcl | hcr
        · have h1 := ihl hdef.1 rl hrl c hcl
          cases hrlc : rl c with
          | none => simp [hrlc] at h1
          | some _ => simp [Row.merge, hrlc]
        · have h2 := ihr hdef.2 rr hrr c hcr
          simp only [Row.merge]
          cases rl c with
          | some _ => rfl
          | none => exact h2
      · cases hcond
  | groupBy keys aggs inner _ =>
    intro r hr c hc
    simp only [eval, List.mem_map] at hr
    rcases hr with ⟨k, hk_mem, rfl⟩
    have hk_in : k ∈ (eval db inner).map (rowKey keys) := mem_dedup.mp hk_mem
    rcases List.mem_map.mp hk_in with ⟨r0, _, rfl⟩
    have hlen : (rowKey keys r0).length = keys.length := by simp [rowKey]
    simp only [buildGroupRow]
    apply setColsFromPairs_isSome
    rw [List.map_append]
    simp only [queryCols, List.mem_append] at hc
    rcases hc with hck | hca
    · exact List.mem_append.mpr (Or.inl (mem_map_fst_zip keys (rowKey keys r0) hlen.symm hck))
    · exact List.mem_append.mpr (Or.inr (by simpa [List.map_map] using hca))
  | unionAll l r ihl ihr =>
    intro row hr c hc
    simp only [allColsDefined, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at hdef
    rcases hdef with ⟨⟨⟨hl, hr_def⟩, hr_in_l⟩, hl_in_r⟩
    simp only [eval, List.mem_append] at hr
    simp only [queryCols, List.mem_append, List.mem_filter] at hc
    have hc_l : c ∈ queryCols l := by
      rcases hc with hcl | ⟨hcr, _⟩
      · exact hcl
      · exact hr_in_l c hcr
    have hc_r : c ∈ queryCols r := hl_in_r c hc_l
    rcases hr with hrow_l | hrow_r
    · exact ihl hl row hrow_l c hc_l
    · exact ihr hr_def row hrow_r c hc_r
  | corrAggFilter o _ _ _ _ _ _ iho _ =>
    intro r hr c hc
    simp only [allColsDefined, Bool.and_eq_true] at hdef
    simp only [eval, List.mem_filter] at hr
    exact iho hdef.1 r hr.1 c hc

theorem evalProjItems_self_of_isSome {cols : List ColName} {r r' : Row}
    (hdom : ∀ c, (r c).isSome = true → c ∈ cols)
    (hsome : ∀ c ∈ cols, (r c).isSome = true)
    (hagree : ∀ c ∈ cols, r' c = r c) :
    evalProjItems (cols.map fun c => ⟨.col c, c⟩) r' = r := by
  funext c
  by_cases hc : c ∈ cols
  · have hproj : ∀ (cs : List ColName), c ∈ cs → (∀ x ∈ cs, r' x = r x) →
        (∀ x ∈ cs, (r x).isSome = true) →
        evalProjItems (cs.map fun x => ⟨.col x, x⟩) r' c = r c := by
      intro cs hcs ha hs
      induction cs with
      | nil => simp at hcs
      | cons x xs ih =>
        simp only [List.map_cons, evalProjItems]
        split
        · rename_i heq
          have hcx : c = x := beq_iff_eq.mp heq
          subst hcx
          simp only [evalExpr, Row.getVal, ha c (List.mem_cons_self ..)]
          have hrc := hs c (List.mem_cons_self ..)
          cases hrc_v : r c with
          | none => simp [hrc_v] at hrc
          | some v => simp
        · rename_i hne
          rcases List.mem_cons.mp hcs with rfl | hmem_xs
          · simp at hne
          · exact ih hmem_xs
              (fun z hz => ha z (List.mem_cons_of_mem x hz))
              (fun z hz => hs z (List.mem_cons_of_mem x hz))
    exact hproj cols hc hagree hsome
  · have hnone_proj : ∀ (cs : List ColName), c ∉ cs →
        evalProjItems (cs.map fun x => ⟨.col x, x⟩) r' c = none := by
      intro cs hnot
      induction cs with
      | nil => rfl
      | cons x xs ih =>
        simp only [List.map_cons, evalProjItems]
        split
        · rename_i heq
          have hcx : c = x := beq_iff_eq.mp heq
          subst hcx
          exact False.elim (hnot (List.mem_cons_self ..))
        · exact ih (fun h => hnot (List.mem_cons_of_mem x h))
    have hnone_r : r c = none := by
      cases hrc : r c with
      | none => rfl
      | some v => exact False.elim (hc (hdom c (by simp [hrc])))
    rw [hnone_r]
    exact hnone_proj cols hc

theorem nodup_filter_length_le_one [BEq α] [LawfulBEq α] {xs : List α} (hnd : xs.Nodup) (a : α) :
    (xs.filter (fun x => x == a)).length ≤ 1 := by
  induction xs with
  | nil => simp
  | cons y ys ih =>
    rw [List.nodup_cons] at hnd
    simp only [List.filter_cons]
    split
    · rename_i heq
      have hya : y = a := beq_iff_eq.mp heq
      subst hya
      have hnil : ys.filter (fun x => x == y) = [] := by
        rw [List.filter_eq_nil_iff]
        intro z hz
        simp only [beq_iff_eq]
        intro hzy
        subst hzy
        exact hnd.1 hz
      simp [hnil]
    · exact ih hnd.2

/-- 追加ルール 3: 相関スカラー集約サブクエリのデコレレーション -/
def decorrelateScalarAggSubqueryRule : VerifiedRule where
  name := "perf.decorrelate_scalar_agg_subquery"
  step schema q :=
    match q with
    | .corrAggFilter outer outerCmpCol cmp inner outerJoinCol innerJoinCol aggOp =>
      let ka := "__subq_key"
      let aa := "__subq_agg"
      let ra := "__raw_agg"
      if isNullOnEmpty aggOp &&
         allColsDefined schema outer &&
         (outerCmpCol ∈ queryCols outer) &&
         (outerJoinCol ∈ queryCols outer) &&
         !(ka ∈ queryCols outer) &&
         !(aa ∈ queryCols outer) &&
         !(innerJoinCol == ra) then
        let subq := Query.project
          [ ⟨.col innerJoinCol, ka⟩, ⟨.col ra, aa⟩ ]
          (Query.groupBy [innerJoinCol] [⟨aggOp, ra⟩] inner)
        let cond := Pred.and
          (.eq (.col outerJoinCol) (.col ka))
          (cmpToPred cmp (.col outerCmpCol) (.col aa))
        some (.project ((queryCols outer).map fun c => ⟨.col c, c⟩) (.innerJoin outer subq cond))
      else
        none
    | _ => none
  preservesCols schema q q' h := by
    cases q with
    | corrAggFilter outer outerCmpCol cmp inner outerJoinCol innerJoinCol aggOp =>
      dsimp only at h
      split at h
      · cases h
        simp [queryCols, List.map_map, Function.comp_def]
      · cases h
    | _ => simp at h
  sound schema q q' h db hdb := by
    cases q with
    | corrAggFilter outer outerCmpCol cmp inner outerJoinCol innerJoinCol aggOp =>
      dsimp only at h
      split at h
      · rename_i hconds
        cases h
        simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq,
          decide_eq_false_iff_not, beq_eq_false_iff_ne] at hconds
        rcases hconds with ⟨⟨⟨⟨⟨⟨hnull_empty, hdef⟩, ho_oc⟩, ho_oj⟩, hka_not⟩, haa_not⟩, hij_ne⟩
        have hka_ne_aa : ("__subq_key" : ColName) ≠ "__subq_agg" := by decide
        let ka : ColName := "__subq_key"
        let aa : ColName := "__subq_agg"
        let ra : ColName := "__raw_agg"
        let innerRows := eval db inner
        let ks := dedup (innerRows.map (rowKey [innerJoinCol]))
        let subq := Query.project
          [ ⟨.col innerJoinCol, ka⟩, ⟨.col ra, aa⟩ ]
          (Query.groupBy [innerJoinCol] [⟨aggOp, ra⟩] inner)
        let jcond := Pred.and
          (.eq (.col outerJoinCol) (.col ka))
          (cmpToPred cmp (.col outerCmpCol) (.col aa))
        -- グループ行を構築したあとの subq 行における ka, aa の値
        have hsubq_vals : ∀ (kv : Val),
            let grp := innerRows.filter (fun ri => rowKey [innerJoinCol] ri == [kv])
            let gr := buildGroupRow [innerJoinCol] [⟨aggOp, ra⟩] [kv] grp
            let sr := evalProjItems [⟨.col innerJoinCol, ka⟩, ⟨.col ra, aa⟩] gr
            sr ka = some kv ∧ sr aa = some (evalAgg aggOp grp) ∧
            ∀ c, c ≠ ka → c ≠ aa → sr c = none := by
          intro kv
          dsimp only
          have hgr_ij : (buildGroupRow [innerJoinCol] [⟨aggOp, ra⟩] [kv]
              (innerRows.filter fun ri => rowKey [innerJoinCol] ri == [kv])) innerJoinCol = some kv := by
            simp [buildGroupRow, setColsFromPairs]
          have hgr_ra : (buildGroupRow [innerJoinCol] [⟨aggOp, ra⟩] [kv]
              (innerRows.filter fun ri => rowKey [innerJoinCol] ri == [kv])) ra =
              some (evalAgg aggOp (innerRows.filter fun ri => rowKey [innerJoinCol] ri == [kv])) := by
            simp only [buildGroupRow, setColsFromPairs, List.zip_cons_cons, List.zip_nil_right,
              List.map_cons, List.map_nil, List.cons_append, List.nil_append]
            have hne : (ra == innerJoinCol) = false := beq_false_of_ne hij_ne.symm
            simp [hne]
          have haa_ka : (aa == ka) = false := beq_false_of_ne hka_ne_aa.symm
          refine ⟨?_, ?_, ?_⟩
          · simp [evalProjItems, evalExpr, Row.getVal, hgr_ij]
          · simp [evalProjItems, evalExpr, Row.getVal, hgr_ra, haa_ka]
          · intro c h1 h2
            simp [evalProjItems, beq_false_of_ne h1, beq_false_of_ne h2]
        -- 各 outer 行 ro に対するマッチの証明
        have hper_ro : ∀ ro ∈ eval db outer,
            ((eval db subq).filterMap fun rr =>
              let m := Row.merge ro rr
              if (evalPred m jcond).isTrue then some m else none).map
                (evalProjItems ((queryCols outer).map fun c => ⟨.col c, c⟩)) =
            if (let kv := Row.getVal ro outerJoinCol
                let grp := innerRows.filter fun ri =>
                  match Row.getVal ri innerJoinCol, kv with
                  | .null, _ => false
                  | _, .null => false
                  | v1, v2 => v1 == v2
                let av := evalAgg aggOp grp
                (evalCmp cmp (Row.getVal ro outerCmpCol) av).isTrue) then [ro] else [] := by
          intro ro hro
          have hro_ka : ro ka = none := row_none_of_not_in_dom hro hka_not
          have hro_aa : ro aa = none := row_none_of_not_in_dom hro haa_not
          have hro_some : ∀ c ∈ queryCols outer, (ro c).isSome = true :=
            allColsDefined_sound hdb hdef ro hro
          have hro_dom : ∀ c, (ro c).isSome = true → c ∈ queryCols outer :=
            eval_row_dom db outer ro hro
          have hmerge_proj : ∀ (kv : Val),
              let grp := innerRows.filter (fun ri => rowKey [innerJoinCol] ri == [kv])
              let sr := evalProjItems [⟨.col innerJoinCol, ka⟩, ⟨.col ra, aa⟩]
                          (buildGroupRow [innerJoinCol] [⟨aggOp, ra⟩] [kv] grp)
              evalProjItems ((queryCols outer).map fun c => ⟨.col c, c⟩) (Row.merge ro sr) = ro := by
            intro kv
            apply evalProjItems_self_of_isSome hro_dom hro_some
            intro c hc
            have hc1 : c ≠ ka := by intro h; rw [h] at hc; exact hka_not hc
            have hc2 : c ≠ aa := by intro h; rw [h] at hc; exact haa_not hc
            have hsr_none := (hsubq_vals kv).2.2 c hc1 hc2
            exact Row.merge_eq_left_of_not_right hsr_none
          have hjcond_eval : ∀ (kv : Val),
              let grp := innerRows.filter (fun ri => rowKey [innerJoinCol] ri == [kv])
              let sr := evalProjItems [⟨.col innerJoinCol, ka⟩, ⟨.col ra, aa⟩]
                          (buildGroupRow [innerJoinCol] [⟨aggOp, ra⟩] [kv] grp)
              (evalPred (Row.merge ro sr) jcond).isTrue =
              (match Row.getVal ro outerJoinCol, kv with
               | .null, _ => false
               | _, .null => false
               | v1, v2 => (v1 == v2) && (evalCmp cmp (Row.getVal ro outerCmpCol) (evalAgg aggOp grp)).isTrue) := by
            intro kv
            dsimp only [jcond]
            have hsr := hsubq_vals kv
            let sr := evalProjItems [⟨.col innerJoinCol, ka⟩, ⟨.col ra, aa⟩]
              (buildGroupRow [innerJoinCol] [⟨aggOp, ra⟩] [kv]
                (innerRows.filter fun ri => rowKey [innerJoinCol] ri == [kv]))
            have hm_ka : Row.merge ro sr ka = some kv := by
              rw [Row.merge_eq_right_of_not_left hro_ka]
              exact hsr.1
            have hm_aa : Row.merge ro sr aa = some (evalAgg aggOp (innerRows.filter fun ri => rowKey [innerJoinCol] ri == [kv])) := by
              rw [Row.merge_eq_right_of_not_left hro_aa]
              exact hsr.2.1
            have hm_oj : Row.merge ro sr outerJoinCol = ro outerJoinCol := by
              apply Row.merge_eq_left_of_not_right
              apply hsr.2.2
              · intro h; rw [h] at ho_oj; exact hka_not ho_oj
              · intro h; rw [h] at ho_oj; exact haa_not ho_oj
            have hm_oc : Row.merge ro sr outerCmpCol = ro outerCmpCol := by
              apply Row.merge_eq_left_of_not_right
              apply hsr.2.2
              · intro h; rw [h] at ho_oc; exact hka_not ho_oc
              · intro h; rw [h] at ho_oc; exact haa_not ho_oc
            have h12 : (evalPred (Row.merge ro sr) jcond).isTrue =
                ((evalPred (Row.merge ro sr) (.eq (.col outerJoinCol) (.col ka))).isTrue &&
                 (evalPred (Row.merge ro sr) (cmpToPred cmp (.col outerCmpCol) (.col aa))).isTrue) := by
              simp only [jcond, evalPred, TriBool.isTrue_and]
            have heq1 : (evalPred (Row.merge ro sr) (.eq (.col outerJoinCol) (.col ka))).isTrue =
                (match Row.getVal ro outerJoinCol, kv with
                 | .null, _ => false
                 | _, .null => false
                 | v1, v2 => v1 == v2) := by
              rw [evalPred_eq_cols_isTrue]
              conv => lhs; rw [hm_oj, hm_ka]
              cases hro_v : ro outerJoinCol with
              | none =>
                simp only [Row.getVal, hro_v, Option.getD_none]
                cases kv <;> rfl
              | some v1 =>
                simp only [Row.getVal, hro_v, Option.getD_some]
                cases v1 <;> cases kv <;> rfl
            have heq2 : (evalPred (Row.merge ro sr) (cmpToPred cmp (.col outerCmpCol) (.col aa))).isTrue =
                (evalCmp cmp (Row.getVal ro outerCmpCol) (evalAgg aggOp (innerRows.filter fun ri => rowKey [innerJoinCol] ri == [kv]))).isTrue := by
              rw [← evalCmp_eq_pred]
              simp only [Row.getVal, hm_oc, hm_aa, Option.getD_some]
            rw [h12, heq1, heq2]
            cases Row.getVal ro outerJoinCol <;> cases kv <;> simp
          -- eval db subq を ks 上の map に展開
          let mkSr : List Val → Row := fun k =>
            evalProjItems [⟨.col innerJoinCol, ka⟩, ⟨.col ra, aa⟩]
              (buildGroupRow [innerJoinCol] [⟨aggOp, ra⟩] k
                (innerRows.filter fun ri => rowKey [innerJoinCol] ri == k))
          have hsubq_eq : eval db subq = ks.map mkSr := by
            simp only [subq, eval, List.map_map, Function.comp_def]
            rfl
          have hks_len : ∀ k ∈ ks, k.length = 1 := by
            intro k hk
            have hk' := mem_dedup.mp hk
            rcases List.mem_map.mp hk' with ⟨ri, _, rfl⟩
            rfl
          -- 共通: ro.outerJoinCol が NULL かどうかで分岐 (重複コードなし)
          by_cases hnull : Row.getVal ro outerJoinCol = .null
          · have hgrp_nil : (innerRows.filter fun ri =>
                match Row.getVal ri innerJoinCol, Row.getVal ro outerJoinCol with
                | .null, _ => false
                | _, .null => false
                | v1, v2 => v1 == v2) = [] := by
              rw [List.filter_eq_nil_iff]
              intro ri _
              rw [hnull]
              cases Row.getVal ri innerJoinCol <;> simp
            have hnull_eval : (evalCmp cmp (Row.getVal ro outerCmpCol) (evalAgg aggOp [])).isTrue = false := by
              rw [evalAgg_nil_of_isNullOnEmpty hnull_empty, evalCmp_null_right]
            simp only [hgrp_nil, hnull_eval, Bool.false_eq_true, if_false]
            have hsubq_nil : ((eval db subq).filterMap fun rr =>
                let m := Row.merge ro rr
                if (evalPred m jcond).isTrue then some m else none) = [] := by
              rw [hsubq_eq]
              have hgen : ∀ (kl : List (List Val)), (∀ k ∈ kl, k.length = 1) →
                  (kl.map mkSr).filterMap (fun rr =>
                    if (evalPred (Row.merge ro rr) jcond).isTrue then some (Row.merge ro rr) else none) = [] := by
                intro kl hkl
                induction kl with
                | nil => rfl
                | cons k kt ih =>
                  have hk1 := hkl k (List.mem_cons_self ..)
                  rcases List.length_eq_one_iff.mp hk1 with ⟨kv, rfl⟩
                  have hj := hjcond_eval kv
                  rw [hnull] at hj
                  simp only [List.map_cons, List.filterMap_cons]
                  dsimp only [mkSr]
                  rw [hj]
                  simp only [Bool.false_eq_true, if_false]
                  exact ih (fun z hz => hkl z (List.mem_cons_of_mem [kv] hz))
              exact hgen ks hks_len
            rw [hsubq_nil]
            rfl
          · let v := Row.getVal ro outerJoinCol
            have hv_def : Row.getVal ro outerJoinCol = v := rfl
            have hgrp_eq :
                (innerRows.filter fun ri =>
                  match Row.getVal ri innerJoinCol, Row.getVal ro outerJoinCol with
                  | .null, _ => false
                  | _, .null => false
                  | v1, v2 => v1 == v2) =
                (innerRows.filter fun ri => rowKey [innerJoinCol] ri == [v]) := by
              congr 1
              funext ri
              simp only [rowKey, List.map_cons, List.map_nil]
              have hlist : ([Row.getVal ri innerJoinCol] == [v]) = (Row.getVal ri innerJoinCol == v) := by
                simp
              rw [hlist, hv_def]
              cases hri : Row.getVal ri innerJoinCol with
              | null =>
                have hne_v : Val.null ≠ v := fun he => hnull he.symm
                simp [beq_false_of_ne hne_v]
              | int _ =>
                cases hv_c : v with
                | null => exact False.elim (hnull hv_c)
                | int _ => rfl
                | str _ => rfl
              | str _ =>
                cases hv_c : v with
                | null => exact False.elim (hnull hv_c)
                | int _ => rfl
                | str _ => rfl
            dsimp only
            simp only [hgrp_eq]
            by_cases hmem_v : [v] ∈ ks
            · -- [v] が ks にちょうど1回存在する場合
              have hex_k : ∃ k ∈ ks, (k == [v]) = true := ⟨[v], hmem_v, by simp⟩
              have huniq_k : (ks.filter (fun k => k == [v])).length ≤ 1 :=
                nodup_filter_length_le_one (nodup_dedup _) [v]
              have hcond_k : ∀ k ∈ ks,
                  (evalPred (Row.merge ro (mkSr k)) jcond).isTrue =
                  ((k == [v]) && (evalCmp cmp (Row.getVal ro outerCmpCol)
                    (evalAgg aggOp (innerRows.filter fun ri => rowKey [innerJoinCol] ri == [v]))).isTrue) := by
                intro k hk
                rcases List.length_eq_one_iff.mp (hks_len k hk) with ⟨kv, rfl⟩
                have hj := hjcond_eval kv
                dsimp only [mkSr]
                rw [hj, hv_def]
                have hlist : ([kv] == [v]) = (kv == v) := by simp
                rw [hlist]
                by_cases hkv_v : kv = v
                · subst hkv_v
                  cases hv_c : v with
                  | null => exact False.elim (hnull hv_c)
                  | int _ => simp
                  | str _ => simp
                · have h1 : (v == kv) = false := beq_false_of_ne (Ne.symm hkv_v)
                  have h2 : (kv == v) = false := beq_false_of_ne hkv_v
                  rw [h2]
                  simp only [Bool.false_and]
                  cases hv_c : v with
                  | null => exact False.elim (hnull hv_c)
                  | int _ =>
                    cases kv with
                    | null => rfl
                    | int _ => rw [hv_c] at h1; simp [h1]
                    | str _ => rfl
                  | str _ =>
                    cases kv with
                    | null => rfl
                    | int _ => rfl
                    | str _ => rw [hv_c] at h1; simp [h1]
              by_cases hcmp_t : (evalCmp cmp (Row.getVal ro outerCmpCol)
                  (evalAgg aggOp (innerRows.filter fun ri => rowKey [innerJoinCol] ri == [v]))).isTrue = true
              · simp only [hcmp_t, if_true]
                rcases filterMap_singleton_of_exists_unique ks (fun k => k == [v])
                    (fun k => Row.merge ro (mkSr k)) hex_k huniq_k with ⟨k0, _, hk0_eq, hfm⟩
                have hk0_v : k0 = [v] := beq_iff_eq.mp hk0_eq
                subst hk0_v
                have hfm_subq :
                    ((eval db subq).filterMap fun rr =>
                      let m := Row.merge ro rr
                      if (evalPred m jcond).isTrue then some m else none) =
                    [Row.merge ro (mkSr [v])] := by
                  rw [hsubq_eq]
                  have hgen : ∀ (kl : List (List Val)), (∀ k ∈ kl, k ∈ ks) →
                      (kl.map mkSr).filterMap (fun rr =>
                        if (evalPred (Row.merge ro rr) jcond).isTrue then some (Row.merge ro rr) else none) =
                      kl.filterMap (fun k =>
                        if (k == [v]) then some (Row.merge ro (mkSr k)) else none) := by
                    intro kl hkl
                    induction kl with
                    | nil => rfl
                    | cons k kt ih =>
                      simp only [List.map_cons, List.filterMap_cons]
                      have hk_cond := hcond_k k (hkl k (List.mem_cons_self ..))
                      rw [hk_cond, hcmp_t, Bool.and_true]
                      have ih' := ih (fun z hz => hkl z (List.mem_cons_of_mem k hz))
                      cases k == [v] <;> simp [ih']
                  rw [hgen ks (fun _ hx => hx)]
                  exact hfm
                rw [hfm_subq]
                simp only [List.map_cons, List.map_nil]
                congr 1
                exact hmerge_proj v
              · have hcmp_f : (evalCmp cmp (Row.getVal ro outerCmpCol)
                    (evalAgg aggOp (innerRows.filter fun ri => rowKey [innerJoinCol] ri == [v]))).isTrue = false :=
                  Bool.eq_false_iff.mpr hcmp_t
                simp only [hcmp_f, Bool.false_eq_true, if_false]
                have hfm_nil :
                    ((eval db subq).filterMap fun rr =>
                      let m := Row.merge ro rr
                      if (evalPred m jcond).isTrue then some m else none) = [] := by
                  rw [hsubq_eq]
                  have hgen : ∀ (kl : List (List Val)), (∀ k ∈ kl, k ∈ ks) →
                      (kl.map mkSr).filterMap (fun rr =>
                        if (evalPred (Row.merge ro rr) jcond).isTrue then some (Row.merge ro rr) else none) = [] := by
                    intro kl hkl
                    induction kl with
                    | nil => rfl
                    | cons k kt ih =>
                      simp only [List.map_cons, List.filterMap_cons]
                      have hk_cond := hcond_k k (hkl k (List.mem_cons_self ..))
                      rw [hk_cond, hcmp_f, Bool.and_false]
                      simp [ih (fun z hz => hkl z (List.mem_cons_of_mem k hz))]
                  exact hgen ks (fun _ hx => hx)
                rw [hfm_nil]
                rfl
            · -- [v] ∉ ks の場合
              have hgrp_empty : (innerRows.filter fun ri => rowKey [innerJoinCol] ri == [v]) = [] := by
                rw [List.filter_eq_nil_iff]
                intro ri hri
                simp only [beq_iff_eq]
                intro heq
                apply hmem_v
                rw [mem_dedup, ← heq]
                exact List.mem_map.mpr ⟨ri, hri, rfl⟩
              have hnull_eval : (evalCmp cmp (Row.getVal ro outerCmpCol) (evalAgg aggOp [])).isTrue = false := by
                rw [evalAgg_nil_of_isNullOnEmpty hnull_empty, evalCmp_null_right]
              simp only [hgrp_empty, hnull_eval, Bool.false_eq_true, if_false]
              have hfm_nil :
                  ((eval db subq).filterMap fun rr =>
                    let m := Row.merge ro rr
                    if (evalPred m jcond).isTrue then some m else none) = [] := by
                rw [hsubq_eq]
                have hgen : ∀ (kl : List (List Val)), (∀ k ∈ kl, k ∈ ks) →
                    (kl.map mkSr).filterMap (fun rr =>
                      if (evalPred (Row.merge ro rr) jcond).isTrue then some (Row.merge ro rr) else none) = [] := by
                  intro kl hkl
                  induction kl with
                  | nil => rfl
                  | cons k kt ih =>
                    have hk_in := hkl k (List.mem_cons_self ..)
                    have hk_ne : k ≠ [v] := fun he => hmem_v (he ▸ hk_in)
                    rcases List.length_eq_one_iff.mp (hks_len k hk_in) with ⟨kv, hkv_eq⟩
                    subst hkv_eq
                    have hkv_ne : kv ≠ v := fun he => hk_ne (by rw [he])
                    have hj := hjcond_eval kv
                    have hj_f : (evalPred (Row.merge ro (mkSr [kv])) jcond).isTrue = false := by
                      dsimp only [mkSr]
                      rw [hj, hv_def]
                      have h1 : (v == kv) = false := beq_false_of_ne (Ne.symm hkv_ne)
                      cases hv_c : v with
                      | null => exact False.elim (hnull hv_c)
                      | int _ =>
                        cases kv with
                        | null => rfl
                        | int _ => rw [hv_c] at h1; simp [h1]
                        | str _ => rfl
                      | str _ =>
                        cases kv with
                        | null => rfl
                        | int _ => rfl
                        | str _ => rw [hv_c] at h1; simp [h1]
                    dsimp only [mkSr] at hj_f
                    simp only [List.map_cons, List.filterMap_cons]
                    rw [hj_f]
                    simp only [Bool.false_eq_true, if_false]
                    exact ih (fun z hz => hkl z (List.mem_cons_of_mem [kv] hz))
                exact hgen ks (fun _ hx => hx)
              rw [hfm_nil]
              rfl
        -- 全体への結合: flatMap (if p ro then [ro] else []) = filter p
        have hwhole : ∀ (ls : List Row), (∀ ro ∈ ls, ro ∈ eval db outer) →
            (ls.flatMap fun ro =>
              ((eval db subq).filterMap fun rr =>
                let m := Row.merge ro rr
                if (evalPred m jcond).isTrue then some m else none).map
                  (evalProjItems ((queryCols outer).map fun c => ⟨.col c, c⟩))) =
            (ls.filter fun ro =>
              let kv := Row.getVal ro outerJoinCol
              let grp := innerRows.filter fun ri =>
                match Row.getVal ri innerJoinCol, kv with
                | .null, _ => false
                | _, .null => false
                | v1, v2 => v1 == v2
              let av := evalAgg aggOp grp
              (evalCmp cmp (Row.getVal ro outerCmpCol) av).isTrue) := by
          intro ls hls
          induction ls with
          | nil => rfl
          | cons ro ros ih =>
            simp only [List.flatMap_cons, List.filter_cons]
            rw [hper_ro ro (hls ro (List.mem_cons_self ..))]
            rw [ih (fun z hz => hls z (List.mem_cons_of_mem ro hz))]
            split <;> simp
        change BagEq
          ((eval db (.innerJoin outer subq jcond)).map (evalProjItems ((queryCols outer).map fun c => ⟨.col c, c⟩)))
          (eval db (.corrAggFilter outer outerCmpCol cmp inner outerJoinCol innerJoinCol aggOp))
        rw [show eval db (.innerJoin outer subq jcond) =
          (eval db outer).flatMap (fun ro =>
            (eval db subq).filterMap fun rr =>
              let m := Row.merge ro rr
              if (evalPred m jcond).isTrue then some m else none) from rfl]
        rw [List.map_flatMap, hwhole (eval db outer) (fun _ hx => hx)]
        exact BagEq.refl _
      · cases h
    | _ => simp at h

/-! ### 追加ルール 4: Eager Aggregation (結合前の事前集約プッシュダウン) -/

def preAlias (idx : Nat) : ColName :=
  "__pre_agg_" ++ toString idx

def isDecomposableAgg (factCols : List ColName) : AggItem → Bool
  | ⟨.sumCol c, _⟩ => c ∈ factCols
  | ⟨.countStar, _⟩ => true
  | ⟨.countCol c, _⟩ => c ∈ factCols
  | ⟨.minCol c, _⟩ => c ∈ factCols
  | ⟨.maxCol c, _⟩ => c ∈ factCols
  | ⟨.avgCol _, _⟩ => false

def toPreAgg (a : AggItem) (idx : Nat) : AggItem :=
  ⟨a.op, preAlias idx⟩

def toPostAgg (a : AggItem) (idx : Nat) : AggItem :=
  let pa := preAlias idx
  let op' :=
    match a.op with
    | .sumCol _ => .sumCol pa
    | .countStar => .sumCol pa
    | .countCol _ => .sumCol pa
    | .minCol _ => .minCol pa
    | .maxCol _ => .maxCol pa
    | .avgCol c => .avgCol c
  ⟨op', a.alias⟩

def mkPreAggs (aggs : List AggItem) (idx : Nat := 0) : List AggItem :=
  match aggs with
  | [] => []
  | a :: rest => toPreAgg a idx :: mkPreAggs rest (idx + 1)

def mkPostAggs (aggs : List AggItem) (idx : Nat := 0) : List AggItem :=
  match aggs with
  | [] => []
  | a :: rest => toPostAgg a idx :: mkPostAggs rest (idx + 1)

def preAliasList (aggs : List AggItem) (idx : Nat := 0) : List ColName :=
  match aggs with
  | [] => []
  | _ :: rest => preAlias idx :: preAliasList rest (idx + 1)

def allDistinct [DecidableEq α] : List α → Bool
  | [] => true
  | x :: xs => !(x ∈ xs) && allDistinct xs

theorem allDistinct_iff_nodup [DecidableEq α] {xs : List α} :
    allDistinct xs = true ↔ xs.Nodup := by
  induction xs with
  | nil => simp [allDistinct]
  | cons x xs ih =>
    simp only [allDistinct, Bool.and_eq_true, Bool.not_eq_true',
      decide_eq_false_iff_not, List.nodup_cons, ih]

/-! #### Eager Aggregation 用の分解補題群 -/

theorem sumNonNullInts_append (c : ColName) (xs ys : List Row) :
    sumNonNullInts c (xs ++ ys) =
    match sumNonNullInts c xs, sumNonNullInts c ys with
    | some a, some b => some (a + b)
    | some a, none => some a
    | none, b => b := by
  induction xs with
  | nil =>
    simp only [List.nil_append, sumNonNullInts]
  | cons x xs ih =>
    simp only [List.cons_append, sumNonNullInts, ih]
    cases Row.getVal x c <;> cases sumNonNullInts c xs <;> cases sumNonNullInts c ys <;> simp
    · omega

theorem countNonNull_append (c : ColName) (xs ys : List Row) :
    countNonNull c (xs ++ ys) = countNonNull c xs + countNonNull c ys := by
  induction xs with
  | nil => simp [countNonNull]
  | cons x xs ih =>
    simp only [List.cons_append, countNonNull, ih]
    cases Row.getVal x c <;> simp <;> omega

theorem minNonNullInt_append (c : ColName) (xs ys : List Row) :
    minNonNullInt c (xs ++ ys) =
    match minNonNullInt c xs, minNonNullInt c ys with
    | some a, some b => some (min a b)
    | some a, none => some a
    | none, b => b := by
  induction xs with
  | nil =>
    simp only [List.nil_append, minNonNullInt]
  | cons x xs ih =>
    simp only [List.cons_append, minNonNullInt, ih]
    cases Row.getVal x c <;> cases minNonNullInt c xs <;> cases minNonNullInt c ys <;> simp

theorem maxNonNullInt_append (c : ColName) (xs ys : List Row) :
    maxNonNullInt c (xs ++ ys) =
    match maxNonNullInt c xs, maxNonNullInt c ys with
    | some a, some b => some (max a b)
    | some a, none => some a
    | none, b => b := by
  induction xs with
  | nil =>
    simp only [List.nil_append, maxNonNullInt]
  | cons x xs ih =>
    simp only [List.cons_append, maxNonNullInt, ih]
    cases Row.getVal x c <;> cases maxNonNullInt c xs <;> cases maxNonNullInt c ys <;> simp

theorem sumNonNullInts_map_congr {c1 c2 : ColName} {f : α → Row} {g : α → Row} (xs : List α)
    (h : ∀ x ∈ xs, Row.getVal (f x) c1 = Row.getVal (g x) c2) :
    sumNonNullInts c1 (xs.map f) = sumNonNullInts c2 (xs.map g) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.map_cons, sumNonNullInts]
    rw [h x (List.mem_cons_self ..), ih (fun z hz => h z (List.mem_cons_of_mem x hz))]

theorem countNonNull_map_congr {c1 c2 : ColName} {f : α → Row} {g : α → Row} (xs : List α)
    (h : ∀ x ∈ xs, Row.getVal (f x) c1 = Row.getVal (g x) c2) :
    countNonNull c1 (xs.map f) = countNonNull c2 (xs.map g) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.map_cons, countNonNull]
    rw [h x (List.mem_cons_self ..), ih (fun z hz => h z (List.mem_cons_of_mem x hz))]

theorem minNonNullInt_map_congr {c1 c2 : ColName} {f : α → Row} {g : α → Row} (xs : List α)
    (h : ∀ x ∈ xs, Row.getVal (f x) c1 = Row.getVal (g x) c2) :
    minNonNullInt c1 (xs.map f) = minNonNullInt c2 (xs.map g) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.map_cons, minNonNullInt]
    rw [h x (List.mem_cons_self ..), ih (fun z hz => h z (List.mem_cons_of_mem x hz))]

theorem maxNonNullInt_map_congr {c1 c2 : ColName} {f : α → Row} {g : α → Row} (xs : List α)
    (h : ∀ x ∈ xs, Row.getVal (f x) c1 = Row.getVal (g x) c2) :
    maxNonNullInt c1 (xs.map f) = maxNonNullInt c2 (xs.map g) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.map_cons, maxNonNullInt]
    rw [h x (List.mem_cons_self ..), ih (fun z hz => h z (List.mem_cons_of_mem x hz))]

theorem evalAgg_map_congr (op : AggOp) {f g : α → Row} (xs : List α)
    (h : ∀ x ∈ xs, ∀ c, Row.getVal (f x) c = Row.getVal (g x) c) :
    evalAgg op (xs.map f) = evalAgg op (xs.map g) := by
  cases op with
  | countStar => simp [evalAgg]
  | countCol c =>
    simp only [evalAgg]
    rw [countNonNull_map_congr xs (fun x hx => h x hx c)]
  | sumCol c =>
    simp only [evalAgg]
    rw [sumNonNullInts_map_congr xs (fun x hx => h x hx c)]
  | avgCol c =>
    simp only [evalAgg]
    rw [sumNonNullInts_map_congr xs (fun x hx => h x hx c)]
    rw [countNonNull_map_congr xs (fun x hx => h x hx c)]
  | minCol c =>
    simp only [evalAgg]
    rw [minNonNullInt_map_congr xs (fun x hx => h x hx c)]
  | maxCol c =>
    simp only [evalAgg]
    rw [maxNonNullInt_map_congr xs (fun x hx => h x hx c)]

theorem setColsFromPairs_lookup {pairs : List (ColName × Val)} {k : ColName} {v : Val}
    (hmem : (k, v) ∈ pairs) (hnodup : (pairs.map Prod.fst).Nodup) :
    setColsFromPairs pairs k = some v := by
  induction pairs with
  | nil => cases hmem
  | cons p ps ih =>
    rcases p with ⟨k', v'⟩
    simp only [List.map_cons, List.nodup_cons] at hnodup
    simp only [setColsFromPairs]
    split
    · rename_i heq
      have hkk' : k = k' := beq_iff_eq.mp heq
      subst hkk'
      rcases List.mem_cons.mp hmem with hpair | hrest
      · cases hpair; rfl
      · have hkin : k ∈ ps.map Prod.fst := List.mem_map.mpr ⟨(k, v), hrest, rfl⟩
        exact False.elim (hnodup.1 hkin)
    · rename_i hne
      rcases List.mem_cons.mp hmem with hpair | hrest
      · cases hpair; simp at hne
      · exact ih hrest hnodup.2

theorem evalAgg_two_stage {β : Type} (parts : List (β × List Row))
    (hne : parts ≠ [])
    (preRow : β → List Row → Row)
    (a : AggItem) (idx : Nat)
    (hdec : match a.op with | .avgCol _ => false | _ => true)
    (hpre : ∀ b grp, (b, grp) ∈ parts →
      Row.getVal (preRow b grp) (preAlias idx) = evalAgg (toPreAgg a idx).op grp) :
    evalAgg (toPostAgg a idx).op (parts.map fun bg => preRow bg.1 bg.2) =
    evalAgg a.op (parts.flatMap Prod.snd) := by
  cases hop : a.op with
  | avgCol _ => simp [hop] at hdec
  | sumCol c =>
    simp only [toPostAgg, hop, evalAgg]
    have hsum : sumNonNullInts (preAlias idx) (parts.map fun bg => preRow bg.1 bg.2) =
        sumNonNullInts c (parts.flatMap Prod.snd) := by
      clear hne
      induction parts with
      | nil => rfl
      | cons bg bgs ih =>
        rcases bg with ⟨b, grp⟩
        have hb := hpre b grp (List.mem_cons_self ..)
        have ih' := ih (fun b' g' hmem => hpre b' g' (List.mem_cons_of_mem (b, grp) hmem))
        simp only [List.map_cons, List.flatMap_cons, sumNonNullInts, sumNonNullInts_append]
        simp only [toPreAgg, hop, evalAgg] at hb
        rw [hb, ih']
        cases sumNonNullInts c grp <;> cases sumNonNullInts c (bgs.flatMap Prod.snd) <;> simp
    rw [hsum]
  | countStar =>
    simp only [toPostAgg, hop, evalAgg]
    have hsum : sumNonNullInts (preAlias idx) (parts.map fun bg => preRow bg.1 bg.2) =
        some ((parts.flatMap Prod.snd).length : Int) := by
      induction parts with
      | nil => exact False.elim (hne rfl)
      | cons bg bgs ih =>
        rcases bg with ⟨b, grp⟩
        have hb := hpre b grp (List.mem_cons_self ..)
        simp only [toPreAgg, hop, evalAgg] at hb
        cases bgs with
        | nil =>
          simp [sumNonNullInts, hb]
        | cons bg2 bgs2 =>
          have ih' := ih (by simp) (fun b' g' hmem => hpre b' g' (List.mem_cons_of_mem (b, grp) hmem))
          simp only [List.map_cons, List.flatMap_cons, sumNonNullInts] at ih' ⊢
          rw [hb, ih']
          simp [Int.natCast_add]
    rw [hsum]
  | countCol c =>
    simp only [toPostAgg, hop, evalAgg]
    have hsum : sumNonNullInts (preAlias idx) (parts.map fun bg => preRow bg.1 bg.2) =
        some (countNonNull c (parts.flatMap Prod.snd) : Int) := by
      induction parts with
      | nil => exact False.elim (hne rfl)
      | cons bg bgs ih =>
        rcases bg with ⟨b, grp⟩
        have hb := hpre b grp (List.mem_cons_self ..)
        simp only [toPreAgg, hop, evalAgg] at hb
        cases bgs with
        | nil =>
          simp [sumNonNullInts, hb]
        | cons bg2 bgs2 =>
          have ih' := ih (by simp) (fun b' g' hmem => hpre b' g' (List.mem_cons_of_mem (b, grp) hmem))
          simp only [List.map_cons, List.flatMap_cons, sumNonNullInts, countNonNull_append] at ih' ⊢
          rw [hb, ih']
          simp [Int.natCast_add]
    rw [hsum]
  | minCol c =>
    simp only [toPostAgg, hop, evalAgg]
    have hmin : minNonNullInt (preAlias idx) (parts.map fun bg => preRow bg.1 bg.2) =
        minNonNullInt c (parts.flatMap Prod.snd) := by
      clear hne
      induction parts with
      | nil => rfl
      | cons bg bgs ih =>
        rcases bg with ⟨b, grp⟩
        have hb := hpre b grp (List.mem_cons_self ..)
        have ih' := ih (fun b' g' hmem => hpre b' g' (List.mem_cons_of_mem (b, grp) hmem))
        simp only [List.map_cons, List.flatMap_cons, minNonNullInt, minNonNullInt_append]
        simp only [toPreAgg, hop, evalAgg] at hb
        rw [hb, ih']
        cases minNonNullInt c grp <;> cases minNonNullInt c (bgs.flatMap Prod.snd) <;> simp
    rw [hmin]
  | maxCol c =>
    simp only [toPostAgg, hop, evalAgg]
    have hmax : maxNonNullInt (preAlias idx) (parts.map fun bg => preRow bg.1 bg.2) =
        maxNonNullInt c (parts.flatMap Prod.snd) := by
      clear hne
      induction parts with
      | nil => rfl
      | cons bg bgs ih =>
        rcases bg with ⟨b, grp⟩
        have hb := hpre b grp (List.mem_cons_self ..)
        have ih' := ih (fun b' g' hmem => hpre b' g' (List.mem_cons_of_mem (b, grp) hmem))
        simp only [List.map_cons, List.flatMap_cons, maxNonNullInt, maxNonNullInt_append]
        simp only [toPreAgg, hop, evalAgg] at hb
        rw [hb, ih']
        cases maxNonNullInt c grp <;> cases maxNonNullInt c (bgs.flatMap Prod.snd) <;> simp
    rw [hmax]

theorem flatMap_cons_option_perm {α β : Type} (xs : List α) (f : α → Option β) (g : α → List β) :
    (xs.flatMap fun x => match f x with | some b => b :: g x | none => g x).Perm
    (xs.filterMap f ++ xs.flatMap g) := by
  induction xs with
  | nil => exact List.Perm.nil
  | cons x xs ih =>
    simp only [List.flatMap_cons, List.filterMap_cons]
    cases hfx : f x with
    | none =>
      have h1 : (g x ++ xs.flatMap fun x => match f x with | some b => b :: g x | none => g x).Perm
          (g x ++ (xs.filterMap f ++ xs.flatMap g)) :=
        (List.Perm.refl (g x)).append ih
      have h2 : (g x ++ (xs.filterMap f ++ xs.flatMap g)).Perm
          (xs.filterMap f ++ (g x ++ xs.flatMap g)) := by
        rw [← List.append_assoc]
        have hp := List.perm_append_comm (l₁ := g x) (l₂ := xs.filterMap f)
        have hp2 := hp.append (List.Perm.refl (xs.flatMap g))
        exact (List.append_assoc (xs.filterMap f) (g x) (xs.flatMap g)) ▸ hp2
      exact h1.trans h2
    | some b =>
      simp only [List.cons_append]
      have h1 : (b :: (g x ++ xs.flatMap fun x => match f x with | some b => b :: g x | none => g x)).Perm
          (b :: (g x ++ (xs.filterMap f ++ xs.flatMap g))) :=
        ((List.Perm.refl (g x)).append ih).cons b
      have h2 : (b :: (g x ++ (xs.filterMap f ++ xs.flatMap g))).Perm
          (b :: (xs.filterMap f ++ (g x ++ xs.flatMap g))) := by
        apply List.Perm.cons b
        rw [← List.append_assoc]
        have hp := List.perm_append_comm (l₁ := g x) (l₂ := xs.filterMap f)
        have hp2 := hp.append (List.Perm.refl (xs.flatMap g))
        exact (List.append_assoc (xs.filterMap f) (g x) (xs.flatMap g)) ▸ hp2
      exact h1.trans h2

theorem flatMap_filterMap_comm {α β γ : Type} (xs : List α) (ys : List β) (f : α → β → Option γ) :
    (xs.flatMap fun x => ys.filterMap fun y => f x y).Perm
    (ys.flatMap fun y => xs.filterMap fun x => f x y) := by
  induction xs with
  | nil =>
    simp only [List.flatMap_nil]
    induction ys with
    | nil => exact List.Perm.nil
    | cons y ys ih => simp [List.flatMap_cons, List.filterMap_nil]
  | cons x xs ih =>
    simp only [List.flatMap_cons]
    have h1 : (ys.filterMap (f x) ++ xs.flatMap fun x => ys.filterMap fun y => f x y).Perm
        (ys.filterMap (f x) ++ ys.flatMap fun y => xs.filterMap fun x => f x y) :=
      (List.Perm.refl _).append ih
    have h2 : (ys.filterMap (f x) ++ ys.flatMap fun y => xs.filterMap fun x => f x y).Perm
        (ys.flatMap fun y => match f x y with | some c => c :: xs.filterMap (fun x' => f x' y) | none => xs.filterMap (fun x' => f x' y)) :=
      (flatMap_cons_option_perm ys (f x) (fun y => xs.filterMap fun x' => f x' y)).symm
    have h3 : (ys.flatMap fun y => match f x y with | some c => c :: xs.filterMap (fun x' => f x' y) | none => xs.filterMap (fun x' => f x' y)) =
        (ys.flatMap fun y => (x :: xs).filterMap fun x' => f x' y) := by
      congr 1
      funext y
      simp only [List.filterMap_cons]
      cases f x y <;> rfl
    rw [← h3]
    exact h1.trans h2

def aggCol : AggOp → Option ColName
  | .countStar => none
  | .countCol c => some c
  | .sumCol c => some c
  | .avgCol c => some c
  | .minCol c => some c
  | .maxCol c => some c

theorem evalAgg_map_congr_on (op : AggOp) {f g : α → Row} (xs : List α)
    (h : ∀ c, aggCol op = some c → ∀ x ∈ xs, Row.getVal (f x) c = Row.getVal (g x) c) :
    evalAgg op (xs.map f) = evalAgg op (xs.map g) := by
  cases op with
  | countStar => simp [evalAgg]
  | countCol c =>
    simp only [evalAgg]
    rw [countNonNull_map_congr xs (h c rfl)]
  | sumCol c =>
    simp only [evalAgg]
    rw [sumNonNullInts_map_congr xs (h c rfl)]
  | avgCol c =>
    simp only [evalAgg]
    rw [sumNonNullInts_map_congr xs (h c rfl), countNonNull_map_congr xs (h c rfl)]
  | minCol c =>
    simp only [evalAgg]
    rw [minNonNullInt_map_congr xs (h c rfl)]
  | maxCol c =>
    simp only [evalAgg]
    rw [maxNonNullInt_map_congr xs (h c rfl)]

theorem isDecomposableAgg_col_in {factCols : List ColName} {a : AggItem}
    (hdec : isDecomposableAgg factCols a = true) {c : ColName} (hc : aggCol a.op = some c) :
    c ∈ factCols := by
  rcases a with ⟨op, al⟩
  cases op with
  | countStar => cases hc
  | countCol c' =>
    cases hc
    simpa [isDecomposableAgg] using hdec
  | sumCol c' =>
    cases hc
    simpa [isDecomposableAgg] using hdec
  | avgCol c' =>
    simp [isDecomposableAgg] at hdec
  | minCol c' =>
    cases hc
    simpa [isDecomposableAgg] using hdec
  | maxCol c' =>
    cases hc
    simpa [isDecomposableAgg] using hdec

theorem mem_preAliasList (aggs : List AggItem) (idx j : Nat) (hj : j < aggs.length) :
    preAlias (idx + j) ∈ preAliasList aggs idx := by
  induction aggs generalizing idx j with
  | nil => simp at hj
  | cons a rest ih =>
    cases j with
    | zero =>
      simp [preAliasList]
    | succ j' =>
      simp only [List.length_cons] at hj
      simp only [preAliasList, List.mem_cons]
      right
      have heq : idx + (j' + 1) = (idx + 1) + j' := by omega
      rw [heq]
      exact ih (idx + 1) j' (by omega)

theorem mkPreAggs_aliases (aggs : List AggItem) (idx : Nat) :
    (mkPreAggs aggs idx).map (·.alias) = preAliasList aggs idx := by
  induction aggs generalizing idx with
  | nil => rfl
  | cons a rest ih =>
    simp only [mkPreAggs, preAliasList, List.map_cons, toPreAgg, ih (idx + 1)]

theorem mkPostAggs_aliases (aggs : List AggItem) (idx : Nat) :
    (mkPostAggs aggs idx).map (·.alias) = aggs.map (·.alias) := by
  induction aggs generalizing idx with
  | nil => rfl
  | cons a rest ih =>
    simp only [mkPostAggs, List.map_cons, toPostAgg, ih (idx + 1)]

theorem preAliasList_cons_mem {aggs : List AggItem} {idx : Nat} {c : ColName} :
    c ∈ preAliasList aggs idx → ∃ j, j < aggs.length ∧ c = preAlias (idx + j) := by
  induction aggs generalizing idx with
  | nil => simp [preAliasList]
  | cons a rest ih =>
    intro hc
    simp only [preAliasList, List.mem_cons] at hc
    rcases hc with rfl | hrest
    · exact ⟨0, by simp, by simp⟩
    · rcases ih hrest with ⟨j, hj, rfl⟩
      refine ⟨j + 1, by simp; omega, ?_⟩
      congr 1
      omega

theorem toPreAgg_mem_mkPreAggs (aggs : List AggItem) (idx j : Nat) (hj : j < aggs.length) :
    (preAlias (idx + j), evalAgg (toPreAgg (aggs[j]'hj) (idx + j)).op grp) ∈
    (mkPreAggs aggs idx).map (fun a => (a.alias, evalAgg a.op grp)) := by
  induction aggs generalizing idx j with
  | nil => simp at hj
  | cons a rest ih =>
    cases j with
    | zero =>
      simp only [mkPreAggs, List.map_cons, toPreAgg, Nat.add_zero, List.getElem_cons_zero]
      exact List.mem_cons_self ..
    | succ j' =>
      simp only [List.length_cons] at hj
      have hj' : j' < rest.length := by omega
      simp only [mkPreAggs, List.map_cons, List.mem_cons]
      right
      have h := ih (idx + 1) j' hj'
      have heq : idx + 1 + j' = idx + (j' + 1) := by omega
      rw [heq] at h
      exact h

theorem mkPreAggs_map_fst (aggs : List AggItem) (idx : Nat) :
    ((mkPreAggs aggs idx).map (fun a => (a.alias, evalAgg a.op grp))).map Prod.fst =
    preAliasList aggs idx := by
  induction aggs generalizing idx with
  | nil => rfl
  | cons a rest ih =>
    simp only [mkPreAggs, preAliasList, List.map_cons, toPreAgg, ih (idx + 1)]

def isNotGroupBy : Query → Bool
  | .groupBy _ _ _ => false
  | _ => true

/-- 追加ルール 4: Eager Aggregation (結合前への事前集約プッシュダウン) -/
def eagerAggThroughJoinRule : VerifiedRule where
  name := "perf.eager_agg_through_join"
  step _ q :=
    match q with
    | .groupBy groupKeys aggs (.innerJoin fact dim cond) =>
      match extractJoinCols fact dim cond with
      | some (factJoinCol, _) =>
        let paList := preAliasList aggs 0
        if !groupKeys.isEmpty &&
           disjointCols (queryCols fact) (queryCols dim) &&
           groupKeys.all (fun c => c ∈ queryCols dim) &&
           allDistinct paList &&
           !(factJoinCol ∈ paList) &&
           disjointCols paList (queryCols dim) &&
           aggs.all (isDecomposableAgg (queryCols fact)) &&
           isNotGroupBy fact then
          let preFact := Query.groupBy [factJoinCol] (mkPreAggs aggs 0) fact
          some (.groupBy groupKeys (mkPostAggs aggs 0) (.innerJoin preFact dim cond))
        else
          none
      | none => none
    | _ => none
  preservesCols schema q q' h := by
    cases q with
    | groupBy groupKeys aggs sub =>
      cases sub with
      | innerJoin fact dim cond =>
        dsimp only at h
        cases hex : extractJoinCols fact dim cond with
        | none => rw [hex] at h; simp at h
        | some pair =>
          rw [hex] at h
          dsimp only at h
          split at h
          · cases h
            simp [queryCols, mkPostAggs_aliases]
          · cases h
      | _ => simp at h
    | _ => simp at h
  sound schema q q' h db _ := by
    cases q with
    | groupBy groupKeys aggs sub =>
      cases sub with
      | innerJoin fact dim cond =>
        dsimp only at h
        cases hex : extractJoinCols fact dim cond with
        | none => rw [hex] at h; simp at h
        | some pair =>
          rw [hex] at h
          rcases pair with ⟨factJoinCol, dimJoinCol⟩
          dsimp only at h
          split at h
          · rename_i hconds
            cases h
            simp only [Bool.and_eq_true, Bool.not_eq_true',
              List.all_eq_true, decide_eq_true_eq, decide_eq_false_iff_not] at hconds
            rcases hconds with ⟨⟨⟨⟨⟨⟨⟨hgk_ne, hdisj_fd⟩, hgk_dim⟩, hpa_dist⟩, hfj_not_pa⟩, hpa_disj_dim⟩, haggs_dec⟩, _⟩
            rw [disjointCols_iff] at hdisj_fd hpa_disj_dim
            rw [allDistinct_iff_nodup] at hpa_dist
            have hjoin_mem : factJoinCol ∈ queryCols fact ∧ dimJoinCol ∈ queryCols dim := by
              simp only [extractJoinCols] at hex
              cases cond with
              | eq e1 e2 =>
                cases e1 <;> cases e2 <;> simp at hex
                case col.col c1 c2 =>
                  split at hex
                  · cases hex; simp_all
                  · split at hex
                    · cases hex; simp_all
                    · cases hex
              | _ => simp at hex
            rcases hjoin_mem with ⟨hfj_in_f, hdj_in_d⟩
            let fs := eval db fact
            let ds := eval db dim
            let preAggs := mkPreAggs aggs 0
            let postAggs := mkPostAggs aggs 0
            let preFact := Query.groupBy [factJoinCol] preAggs fact
            -- 1) cond を factJoinCol と dimJoinCol の単純比較に正規化
            have hcond_eq : ∀ (r1 r2 : Row) (c_not_d : r2 factJoinCol = none) (c_not_f : r1 dimJoinCol = none),
                (evalPred (Row.merge r1 r2) cond).isTrue =
                (match r1 factJoinCol, r2 dimJoinCol with
                 | some (.null), _ => false
                 | _, some (.null) => false
                 | some v1, some v2 => v1 == v2
                 | _, _ => false) := by
              intro r1 r2 c_not_d c_not_f
              have hm1 : Row.merge r1 r2 factJoinCol = r1 factJoinCol :=
                Row.merge_eq_left_of_not_right c_not_d
              have hm2 : Row.merge r1 r2 dimJoinCol = r2 dimJoinCol :=
                Row.merge_eq_right_of_not_left c_not_f
              simp only [extractJoinCols] at hex
              cases cond with
              | eq e1 e2 =>
                cases e1 <;> cases e2 <;> simp at hex
                case col.col c1 c2 =>
                  split at hex
                  · rcases hex with ⟨rfl, rfl⟩
                    rw [evalPred_eq_cols_isTrue, hm1, hm2]
                  · split at hex
                    · rcases hex with ⟨rfl, rfl⟩
                      rw [evalPred_eq_cols_isTrue, hm1, hm2]
                      cases r1 factJoinCol with
                      | none => cases r2 dimJoinCol with | none => rfl | some v2 => cases v2 <;> rfl
                      | some v1 =>
                        cases r2 dimJoinCol with
                        | none => cases v1 <;> rfl
                        | some v2 => cases v1 <;> cases v2 <;> simp [val_beq_comm]
                    · cases hex
              | _ => simp at hex
            -- preFact の出力列に対する行と値を整理
            let ks_f := dedup (fs.map (rowKey [factJoinCol]))
            let preGroup : Val → List Row := fun v => fs.filter (fun rf => rowKey [factJoinCol] rf == [v])
            let preRow : Val → Row := fun v =>
              buildGroupRow [factJoinCol] preAggs [v] (preGroup v)
            have hpre_vals : ∀ (v : Val),
                preRow v factJoinCol = some v ∧
                (∀ (j : Nat) (hj : j < aggs.length),
                  (preRow v) (preAlias (0 + j)) =
                    some (evalAgg (toPreAgg (aggs[j]'hj) (0 + j)).op (preGroup v))) ∧
                (∀ c, c ≠ factJoinCol → c ∉ preAliasList aggs 0 → preRow v c = none) := by
              intro v
              refine ⟨?_, ?_, ?_⟩
              · simp [preRow, buildGroupRow, setColsFromPairs]
              · intro j hj
                simp only [preRow, buildGroupRow]
                apply setColsFromPairs_lookup
                · rw [List.mem_append]
                  right
                  exact toPreAgg_mem_mkPreAggs aggs 0 j hj
                · rw [List.map_append, List.nodup_append]
                  have hmk_fst := mkPreAggs_map_fst aggs 0 (grp := preGroup v)
                  refine ⟨by simp, ?_, ?_⟩
                  · rw [hmk_fst]
                    exact hpa_dist
                  · intro a ha b hb heq
                    simp only [List.zip_cons_cons, List.zip_nil_right, List.map_cons,
                      List.map_nil, List.mem_singleton] at ha
                    subst ha
                    rw [hmk_fst] at hb
                    rw [← heq] at hb
                    exact hfj_not_pa hb
              · intro c hne1 hnotpa
                simp only [preRow, buildGroupRow, List.zip_cons_cons, List.zip_nil_right]
                have hnone_aux : ∀ (pairs : List (ColName × Val)),
                    c ∉ pairs.map Prod.fst → setColsFromPairs pairs c = none := by
                  intro pairs hnot
                  induction pairs with
                  | nil => rfl
                  | cons p ps ih =>
                    rcases p with ⟨k, val⟩
                    simp only [List.map_cons, List.mem_cons, not_or] at hnot
                    simp only [setColsFromPairs, beq_false_of_ne hnot.1]
                    exact ih hnot.2
                apply hnone_aux
                rw [List.map_append]
                simp only [List.map_cons, List.map_nil, List.mem_append, List.mem_singleton, not_or]
                refine ⟨hne1, ?_⟩
                rw [mkPreAggs_map_fst]
                exact hnotpa
            -- preFact の eval は ks_f.map (fun k => ...) であり各 k は [v]
            have hks_f_len : ∀ k ∈ ks_f, k.length = 1 := by
              intro k hk
              rcases List.mem_map.mp (mem_dedup.mp hk) with ⟨rf, _, rfl⟩
              rfl
            -- fact と dim の元の innerJoin (dim を外側に交換)
            let origDimJoin : Bag := ds.flatMap fun rd =>
              fs.filterMap fun rf =>
                let m := Row.merge rf rd
                if (evalPred m cond).isTrue then some m else none
            let preDimJoin : Bag := ds.flatMap fun rd =>
              (eval db preFact).filterMap fun rp =>
                let m := Row.merge rp rd
                if (evalPred m cond).isTrue then some m else none
            have horig_perm : (eval db (.innerJoin fact dim cond)).Perm origDimJoin := by
              simp only [eval]
              exact flatMap_filterMap_comm fs ds (fun rf rd =>
                let m := Row.merge rf rd
                if (evalPred m cond).isTrue then some m else none)
            have hpre_perm : (eval db (.innerJoin preFact dim cond)).Perm preDimJoin := by
              simp only [eval]
              exact flatMap_filterMap_comm (eval db preFact) ds (fun rp rd =>
                let m := Row.merge rp rd
                if (evalPred m cond).isTrue then some m else none)
            -- 各 rd ∈ ds に対し、origDimJoin でのマッチリストと preDimJoin でのマッチリストを明示
            let rdMatchKey (rd : Row) : Option Val :=
              match rd dimJoinCol with
              | some .null => none
              | some v => some v
              | none => none
            have hfact_match_eq : ∀ rd ∈ ds,
                (fs.filterMap fun rf =>
                  let m := Row.merge rf rd
                  if (evalPred m cond).isTrue then some m else none) =
                (match rdMatchKey rd with
                 | none => []
                 | some v => (preGroup v).map (fun rf => Row.merge rf rd)) := by
              intro rd hrd
              have hfj_not_d : factJoinCol ∉ queryCols dim := hdisj_fd factJoinCol hfj_in_f
              have hc1 : rd factJoinCol = none := row_none_of_not_in_dom hrd hfj_not_d
              have h_inner : ∀ (fl : List Row), (∀ rf ∈ fl, rf ∈ fs) →
                  (fl.filterMap fun rf =>
                    let m := Row.merge rf rd
                    if (evalPred m cond).isTrue then some m else none) =
                  (match rdMatchKey rd with
                   | none => []
                   | some v => (fl.filter fun rf => rowKey [factJoinCol] rf == [v]).map (fun rf => Row.merge rf rd)) := by
                intro fl hfl
                induction fl with
                | nil => cases rdMatchKey rd <;> rfl
                | cons rf rfs ih =>
                  have hrf := hfl rf (List.mem_cons_self ..)
                  have hdj_not_f : dimJoinCol ∉ queryCols fact := by
                    intro hm; exact hdisj_fd dimJoinCol hm hdj_in_d
                  have hc2 : rf dimJoinCol = none := row_none_of_not_in_dom hrf hdj_not_f
                  have hce := hcond_eq rf rd hc1 hc2
                  have ih' := ih (fun z hz => hfl z (List.mem_cons_of_mem rf hz))
                  simp only [List.filterMap_cons, rdMatchKey] at ih' ⊢
                  cases hrd_dj : rd dimJoinCol with
                  | none =>
                    rw [hrd_dj] at hce ih'
                    have hce' : (evalPred (Row.merge rf rd) cond).isTrue = false := by
                      rw [hce]
                      cases rf factJoinCol with
                      | none => rfl
                      | some fv => cases fv <;> rfl
                    simp only [hce', Bool.false_eq_true, if_false]
                    exact ih'
                  | some dv =>
                    cases dv with
                    | null =>
                      rw [hrd_dj] at hce ih'
                      have hce' : (evalPred (Row.merge rf rd) cond).isTrue = false := by
                        rw [hce]
                        cases rf factJoinCol with
                        | none => rfl
                        | some fv => cases fv <;> rfl
                      simp only [hce', Bool.false_eq_true, if_false]
                      exact ih'
                    | int n =>
                      rw [hrd_dj] at hce ih'
                      dsimp only
                      simp only [List.filter_cons]
                      have hrk : (rowKey [factJoinCol] rf == [Val.int n]) =
                          (evalPred (Row.merge rf rd) cond).isTrue := by
                        rw [hce]
                        simp only [rowKey, List.map_cons, List.map_nil, Row.getVal]
                        cases hrf_fj : rf factJoinCol with
                        | none => rfl
                        | some fv =>
                          cases fv with
                          | null => rfl
                          | int m =>
                            simp only [Option.getD_some]
                            by_cases hmn : m = n
                            · subst hmn; simp
                            · simp
                          | str _ => rfl
                      rw [hrk]
                      cases (evalPred (Row.merge rf rd) cond).isTrue <;> simp [ih']
                    | str s =>
                      rw [hrd_dj] at hce ih'
                      dsimp only
                      simp only [List.filter_cons]
                      have hrk : (rowKey [factJoinCol] rf == [Val.str s]) =
                          (evalPred (Row.merge rf rd) cond).isTrue := by
                        rw [hce]
                        simp only [rowKey, List.map_cons, List.map_nil, Row.getVal]
                        cases hrf_fj : rf factJoinCol with
                        | none => rfl
                        | some fv =>
                          cases fv with
                          | null => rfl
                          | int _ => rfl
                          | str s' =>
                            simp only [Option.getD_some]
                            by_cases hss : s' = s
                            · subst hss; simp
                            · simp
                      rw [hrk]
                      cases (evalPred (Row.merge rf rd) cond).isTrue <;> simp [ih']
              exact h_inner fs (fun _ hx => hx)
            have hpre_match_eq : ∀ rd ∈ ds,
                ((eval db preFact).filterMap fun rp =>
                  let m := Row.merge rp rd
                  if (evalPred m cond).isTrue then some m else none) =
                (match rdMatchKey rd with
                 | none => []
                 | some v => if [v] ∈ ks_f then [Row.merge (preRow v) rd] else []) := by
              intro rd hrd
              have hfj_not_d : factJoinCol ∉ queryCols dim := hdisj_fd factJoinCol hfj_in_f
              have hc1 : rd factJoinCol = none := row_none_of_not_in_dom hrd hfj_not_d
              have hdj_not_pre : dimJoinCol ∉ queryCols preFact := by
                intro hm
                simp only [preFact, queryCols] at hm
                have hm' : dimJoinCol = factJoinCol ∨ dimJoinCol ∈ preAggs.map (·.alias) := by
                  simpa [List.mem_append, List.map_map] using hm
                rcases hm' with rfl | hm_pa
                · exact hdisj_fd dimJoinCol hfj_in_f hdj_in_d
                · have hmem_pa : dimJoinCol ∈ preAliasList aggs 0 := by
                    dsimp only [preAggs] at hm_pa
                    rw [mkPreAggs_aliases] at hm_pa
                    exact hm_pa
                  exact hpa_disj_dim dimJoinCol hmem_pa hdj_in_d
              have hpre_eval_eq : eval db preFact = ks_f.map (fun k =>
                  buildGroupRow [factJoinCol] preAggs k (fs.filter (fun r => rowKey [factJoinCol] r == k))) := rfl
              rw [hpre_eval_eq]
              cases hrd_dj : rd dimJoinCol with
              | none =>
                simp only [rdMatchKey, hrd_dj]
                have hnil : ∀ (kl : List (List Val)), (∀ k ∈ kl, k.length = 1) →
                    ((kl.map (fun k => buildGroupRow [factJoinCol] preAggs k (fs.filter (fun r => rowKey [factJoinCol] r == k)))).filterMap
                      fun rp => if (evalPred (Row.merge rp rd) cond).isTrue then some (Row.merge rp rd) else none) = [] := by
                  intro kl hkl
                  induction kl with
                  | nil => rfl
                  | cons k kt ih =>
                    rcases List.length_eq_one_iff.mp (hkl k (List.mem_cons_self ..)) with ⟨kv, rfl⟩
                    have hc2 : (preRow kv) dimJoinCol = none := by
                      apply (hpre_vals kv).2.2
                      · intro h; exact hdisj_fd factJoinCol hfj_in_f (h ▸ hdj_in_d)
                      · intro h; exact hpa_disj_dim dimJoinCol h hdj_in_d
                    have hce := hcond_eq (preRow kv) rd hc1 hc2
                    rw [hrd_dj] at hce
                    have hce' : (evalPred (Row.merge (preRow kv) rd) cond).isTrue = false := by
                      rw [hce]
                      cases (preRow kv) factJoinCol with
                      | none => rfl
                      | some fv => cases fv <;> rfl
                    simp only [List.map_cons, List.filterMap_cons]
                    dsimp only [preRow, preGroup] at hce'
                    rw [hce']
                    simp only [Bool.false_eq_true, if_false]
                    exact ih (fun z hz => hkl z (List.mem_cons_of_mem [kv] hz))
                exact hnil ks_f hks_f_len
              | some dv =>
                cases dv with
                | null =>
                  simp only [rdMatchKey, hrd_dj]
                  have hnil : ∀ (kl : List (List Val)), (∀ k ∈ kl, k.length = 1) →
                      ((kl.map (fun k => buildGroupRow [factJoinCol] preAggs k (fs.filter (fun r => rowKey [factJoinCol] r == k)))).filterMap
                        fun rp => if (evalPred (Row.merge rp rd) cond).isTrue then some (Row.merge rp rd) else none) = [] := by
                    intro kl hkl
                    induction kl with
                    | nil => rfl
                    | cons k kt ih =>
                      rcases List.length_eq_one_iff.mp (hkl k (List.mem_cons_self ..)) with ⟨kv, rfl⟩
                      have hc2 : (preRow kv) dimJoinCol = none := by
                        apply (hpre_vals kv).2.2
                        · intro h; exact hdisj_fd factJoinCol hfj_in_f (h ▸ hdj_in_d)
                        · intro h; exact hpa_disj_dim dimJoinCol h hdj_in_d
                      have hce := hcond_eq (preRow kv) rd hc1 hc2
                      rw [hrd_dj] at hce
                      have hce' : (evalPred (Row.merge (preRow kv) rd) cond).isTrue = false := by
                        rw [hce]
                        cases (preRow kv) factJoinCol with
                        | none => rfl
                        | some fv => cases fv <;> rfl
                      simp only [List.map_cons, List.filterMap_cons]
                      dsimp only [preRow, preGroup] at hce'
                      rw [hce']
                      simp only [Bool.false_eq_true, if_false]
                      exact ih (fun z hz => hkl z (List.mem_cons_of_mem [kv] hz))
                  exact hnil ks_f hks_f_len
                | int n =>
                  dsimp only [rdMatchKey]
                  rw [hrd_dj]
                  dsimp only
                  have hpred_k : ∀ k ∈ ks_f,
                      (evalPred (Row.merge (buildGroupRow [factJoinCol] preAggs k (fs.filter (fun r => rowKey [factJoinCol] r == k))) rd) cond).isTrue =
                      (k == [Val.int n]) := by
                    intro k hk
                    rcases List.length_eq_one_iff.mp (hks_f_len k hk) with ⟨kv, rfl⟩
                    have hc2 : (buildGroupRow [factJoinCol] preAggs [kv] (fs.filter (fun r => rowKey [factJoinCol] r == [kv]))) dimJoinCol = none := by
                      apply (hpre_vals kv).2.2
                      · intro h; exact hdisj_fd factJoinCol hfj_in_f (h ▸ hdj_in_d)
                      · intro h; exact hpa_disj_dim dimJoinCol h hdj_in_d
                    have hce := hcond_eq _ rd hc1 hc2
                    have hfj_eq : buildGroupRow [factJoinCol] preAggs [kv] (fs.filter (fun r => rowKey [factJoinCol] r == [kv])) factJoinCol = some kv :=
                      (hpre_vals kv).1
                    rw [hce, hrd_dj, hfj_eq]
                    cases kv with
                    | null => simp
                    | int m =>
                      by_cases hmn : m = n
                      · subst hmn; simp
                      · simp
                    | str _ => simp
                  by_cases hmem : [Val.int n] ∈ ks_f
                  · simp only [hmem, if_true]
                    have hex_k : ∃ k ∈ ks_f, (k == [Val.int n]) = true := ⟨[Val.int n], hmem, by simp⟩
                    have huniq_k : (ks_f.filter (fun k => k == [Val.int n])).length ≤ 1 :=
                      nodup_filter_length_le_one (nodup_dedup _) [Val.int n]
                    rcases filterMap_singleton_of_exists_unique ks_f (fun k => k == [Val.int n])
                        (fun k => Row.merge (buildGroupRow [factJoinCol] preAggs k (fs.filter (fun r => rowKey [factJoinCol] r == k))) rd)
                        hex_k huniq_k with ⟨k0, _, hk0_eq, hfm⟩
                    have hk0_v : k0 = [Val.int n] := beq_iff_eq.mp hk0_eq
                    subst hk0_v
                    have hgen : ∀ (kl : List (List Val)), (∀ k ∈ kl, k ∈ ks_f) →
                        (kl.map (fun k => buildGroupRow [factJoinCol] preAggs k (fs.filter (fun r => rowKey [factJoinCol] r == k)))).filterMap
                          (fun rp => if (evalPred (Row.merge rp rd) cond).isTrue then some (Row.merge rp rd) else none) =
                        kl.filterMap (fun k => if (k == [Val.int n]) then
                          some (Row.merge (buildGroupRow [factJoinCol] preAggs k (fs.filter (fun r => rowKey [factJoinCol] r == k))) rd) else none) := by
                      intro kl hkl
                      induction kl with
                      | nil => rfl
                      | cons k kt ih =>
                        simp only [List.map_cons, List.filterMap_cons]
                        rw [hpred_k k (hkl k (List.mem_cons_self ..))]
                        have ih' := ih (fun z hz => hkl z (List.mem_cons_of_mem k hz))
                        cases k == [Val.int n] <;> simp [ih']
                    rw [hgen ks_f (fun _ hx => hx)]
                    exact hfm
                  · simp only [hmem, if_false]
                    have hgen : ∀ (kl : List (List Val)), (∀ k ∈ kl, k ∈ ks_f) →
                        (kl.map (fun k => buildGroupRow [factJoinCol] preAggs k (fs.filter (fun r => rowKey [factJoinCol] r == k)))).filterMap
                          (fun rp => if (evalPred (Row.merge rp rd) cond).isTrue then some (Row.merge rp rd) else none) = [] := by
                      intro kl hkl
                      induction kl with
                      | nil => rfl
                      | cons k kt ih =>
                        have hk_in := hkl k (List.mem_cons_self ..)
                        have hne : k ≠ [Val.int n] := fun he => hmem (he ▸ hk_in)
                        simp only [List.map_cons, List.filterMap_cons]
                        rw [hpred_k k hk_in, beq_false_of_ne hne]
                        simp only [Bool.false_eq_true, if_false]
                        exact ih (fun z hz => hkl z (List.mem_cons_of_mem k hz))
                    exact hgen ks_f (fun _ hx => hx)
                | str s =>
                  dsimp only [rdMatchKey]
                  rw [hrd_dj]
                  dsimp only
                  have hpred_k : ∀ k ∈ ks_f,
                      (evalPred (Row.merge (buildGroupRow [factJoinCol] preAggs k (fs.filter (fun r => rowKey [factJoinCol] r == k))) rd) cond).isTrue =
                      (k == [Val.str s]) := by
                    intro k hk
                    rcases List.length_eq_one_iff.mp (hks_f_len k hk) with ⟨kv, rfl⟩
                    have hc2 : (buildGroupRow [factJoinCol] preAggs [kv] (fs.filter (fun r => rowKey [factJoinCol] r == [kv]))) dimJoinCol = none := by
                      apply (hpre_vals kv).2.2
                      · intro h; exact hdisj_fd factJoinCol hfj_in_f (h ▸ hdj_in_d)
                      · intro h; exact hpa_disj_dim dimJoinCol h hdj_in_d
                    have hce := hcond_eq _ rd hc1 hc2
                    have hfj_eq : buildGroupRow [factJoinCol] preAggs [kv] (fs.filter (fun r => rowKey [factJoinCol] r == [kv])) factJoinCol = some kv :=
                      (hpre_vals kv).1
                    rw [hce, hrd_dj, hfj_eq]
                    cases kv with
                    | null => simp
                    | int _ => simp
                    | str s' =>
                      by_cases hss : s' = s
                      · subst hss; simp
                      · simp
                  by_cases hmem : [Val.str s] ∈ ks_f
                  · simp only [hmem, if_true]
                    have hex_k : ∃ k ∈ ks_f, (k == [Val.str s]) = true := ⟨[Val.str s], hmem, by simp⟩
                    have huniq_k : (ks_f.filter (fun k => k == [Val.str s])).length ≤ 1 :=
                      nodup_filter_length_le_one (nodup_dedup _) [Val.str s]
                    rcases filterMap_singleton_of_exists_unique ks_f (fun k => k == [Val.str s])
                        (fun k => Row.merge (buildGroupRow [factJoinCol] preAggs k (fs.filter (fun r => rowKey [factJoinCol] r == k))) rd)
                        hex_k huniq_k with ⟨k0, _, hk0_eq, hfm⟩
                    have hk0_v : k0 = [Val.str s] := beq_iff_eq.mp hk0_eq
                    subst hk0_v
                    have hgen : ∀ (kl : List (List Val)), (∀ k ∈ kl, k ∈ ks_f) →
                        (kl.map (fun k => buildGroupRow [factJoinCol] preAggs k (fs.filter (fun r => rowKey [factJoinCol] r == k)))).filterMap
                          (fun rp => if (evalPred (Row.merge rp rd) cond).isTrue then some (Row.merge rp rd) else none) =
                        kl.filterMap (fun k => if (k == [Val.str s]) then
                          some (Row.merge (buildGroupRow [factJoinCol] preAggs k (fs.filter (fun r => rowKey [factJoinCol] r == k))) rd) else none) := by
                      intro kl hkl
                      induction kl with
                      | nil => rfl
                      | cons k kt ih =>
                        simp only [List.map_cons, List.filterMap_cons]
                        rw [hpred_k k (hkl k (List.mem_cons_self ..))]
                        have ih' := ih (fun z hz => hkl z (List.mem_cons_of_mem k hz))
                        cases k == [Val.str s] <;> simp [ih']
                    rw [hgen ks_f (fun _ hx => hx)]
                    exact hfm
                  · simp only [hmem, if_false]
                    have hgen : ∀ (kl : List (List Val)), (∀ k ∈ kl, k ∈ ks_f) →
                        (kl.map (fun k => buildGroupRow [factJoinCol] preAggs k (fs.filter (fun r => rowKey [factJoinCol] r == k)))).filterMap
                          (fun rp => if (evalPred (Row.merge rp rd) cond).isTrue then some (Row.merge rp rd) else none) = [] := by
                      intro kl hkl
                      induction kl with
                      | nil => rfl
                      | cons k kt ih =>
                        have hk_in := hkl k (List.mem_cons_self ..)
                        have hne : k ≠ [Val.str s] := fun he => hmem (he ▸ hk_in)
                        simp only [List.map_cons, List.filterMap_cons]
                        rw [hpred_k k hk_in, beq_false_of_ne hne]
                        simp only [Bool.false_eq_true, if_false]
                        exact ih (fun z hz => hkl z (List.mem_cons_of_mem k hz))
                    exact hgen ks_f (fun _ hx => hx)
            -- 2) origDimJoin と preDimJoin に対して groupBy 全体を照合
            -- 任意の rd ∈ ds について rowKey groupKeys (Row.merge r1 rd) = rowKey groupKeys rd
            have hrk_merge : ∀ (r1 rd : Row), (∀ c ∈ groupKeys, r1 c = none) →
                rowKey groupKeys (Row.merge r1 rd) = rowKey groupKeys rd := by
              intro r1 rd hnone
              simp only [rowKey]
              apply List.map_congr_left
              intro c hc
              simp only [Row.getVal, Row.merge_eq_right_of_not_left (hnone c hc)]
            -- eval_groupBy_congr を使って innerJoin の左右の並びを ds 外側に揃える
            have horig_gb : BagEq
                (eval db (.groupBy groupKeys aggs (.innerJoin fact dim cond)))
                (let ks0 := dedup (origDimJoin.map (rowKey groupKeys))
                 ks0.map fun k => buildGroupRow groupKeys aggs k (origDimJoin.filter fun r => rowKey groupKeys r == k)) :=
              by
                -- eval_groupBy_congr と同じ理由 (origDimJoin と Perm)
                have hks := perm_dedup (List.Perm.map (rowKey groupKeys) horig_perm)
                have h1 := hks.map (fun k => buildGroupRow groupKeys aggs k ((eval db (.innerJoin fact dim cond)).filter fun r => rowKey groupKeys r == k))
                have h2 :
                    ((dedup (origDimJoin.map (rowKey groupKeys))).map fun k =>
                      buildGroupRow groupKeys aggs k ((eval db (.innerJoin fact dim cond)).filter fun r => rowKey groupKeys r == k)) =
                    ((dedup (origDimJoin.map (rowKey groupKeys))).map fun k =>
                      buildGroupRow groupKeys aggs k (origDimJoin.filter fun r => rowKey groupKeys r == k)) := by
                  apply List.map_congr_left
                  intro k _
                  exact buildGroupRow_perm groupKeys aggs k (horig_perm.filter _)
                rw [h2] at h1
                exact h1
            have hpre_gb : BagEq
                (eval db (.groupBy groupKeys postAggs (.innerJoin preFact dim cond)))
                (let ks1 := dedup (preDimJoin.map (rowKey groupKeys))
                 ks1.map fun k => buildGroupRow groupKeys postAggs k (preDimJoin.filter fun r => rowKey groupKeys r == k)) :=
              by
                have hks := perm_dedup (List.Perm.map (rowKey groupKeys) hpre_perm)
                have h1 := hks.map (fun k => buildGroupRow groupKeys postAggs k ((eval db (.innerJoin preFact dim cond)).filter fun r => rowKey groupKeys r == k))
                have h2 :
                    ((dedup (preDimJoin.map (rowKey groupKeys))).map fun k =>
                      buildGroupRow groupKeys postAggs k ((eval db (.innerJoin preFact dim cond)).filter fun r => rowKey groupKeys r == k)) =
                    ((dedup (preDimJoin.map (rowKey groupKeys))).map fun k =>
                      buildGroupRow groupKeys postAggs k (preDimJoin.filter fun r => rowKey groupKeys r == k)) := by
                  apply List.map_congr_left
                  intro k _
                  exact buildGroupRow_perm groupKeys postAggs k (hpre_perm.filter _)
                rw [h2] at h1
                exact h1
            -- ds 内の有効行判定 (rdMatchKey rd = some v かつ [v] ∈ ks_f)
            let rdMatches : Row → Bool := fun rd =>
              match rdMatchKey rd with
              | none => false
              | some v => decide ([v] ∈ ks_f)
            have hpreGroup_nonempty_iff : ∀ v, [v] ∈ ks_f ↔ preGroup v ≠ [] := by
              intro v
              constructor
              · intro hmem
                have hmem' := mem_dedup.mp hmem
                rcases List.mem_map.mp hmem' with ⟨rf, hrf, hrk⟩
                intro hnil
                have : rf ∈ preGroup v := List.mem_filter.mpr ⟨hrf, beq_iff_eq.mpr hrk⟩
                rw [hnil] at this
                cases this
              · intro hne
                cases hg : preGroup v with
                | nil => exact False.elim (hne hg)
                | cons rf _ =>
                  have hmem : rf ∈ preGroup v := by rw [hg]; exact List.mem_cons_self ..
                  rcases List.mem_filter.mp hmem with ⟨hrf, hrk⟩
                  rw [mem_dedup]
                  exact List.mem_map.mpr ⟨rf, hrf, beq_iff_eq.mp hrk⟩
            -- キー集合の一致: k ∈ origDimJoin.map (rowKey groupKeys) ↔ k ∈ preDimJoin.map (rowKey groupKeys) ↔ ∃ rd ∈ ds, rdMatches rd ∧ rowKey groupKeys rd = k
            have hkeys_iff : ∀ k,
                (k ∈ origDimJoin.map (rowKey groupKeys)) ↔
                (∃ rd ∈ ds, rdMatches rd = true ∧ rowKey groupKeys rd = k) := by
              intro k
              constructor
              · intro hk
                rcases List.mem_map.mp hk with ⟨m, hm, rfl⟩
                simp only [origDimJoin, List.mem_flatMap] at hm
                rcases hm with ⟨rd, hrd, hm_rd⟩
                rw [hfact_match_eq rd hrd] at hm_rd
                cases hrm : rdMatchKey rd with
                | none => rw [hrm] at hm_rd; simp at hm_rd
                | some v =>
                  rw [hrm] at hm_rd
                  rcases List.mem_map.mp hm_rd with ⟨rf, hrf, rfl⟩
                  have hrf_f : rf ∈ fs := (List.mem_filter.mp hrf).1
                  have hrk_eq : rowKey groupKeys (Row.merge rf rd) = rowKey groupKeys rd := by
                    apply hrk_merge
                    intro c hc
                    apply row_none_of_not_in_dom hrf_f
                    intro hm_f
                    exact hdisj_fd c hm_f (hgk_dim c hc)
                  refine ⟨rd, hrd, ?_, hrk_eq.symm⟩
                  simp only [rdMatches, hrm, decide_eq_true_eq]
                  rw [hpreGroup_nonempty_iff]
                  intro hnil
                  rw [hnil] at hrf
                  cases hrf
              · rintro ⟨rd, hrd, hmatch, rfl⟩
                simp only [rdMatches] at hmatch
                cases hrm : rdMatchKey rd with
                | none => rw [hrm] at hmatch; simp at hmatch
                | some v =>
                  rw [hrm] at hmatch
                  simp only [decide_eq_true_eq] at hmatch
                  have hne := (hpreGroup_nonempty_iff v).mp hmatch
                  cases hg : preGroup v with
                  | nil => exact False.elim (hne hg)
                  | cons rf _ =>
                    have hrf : rf ∈ preGroup v := by rw [hg]; exact List.mem_cons_self ..
                    have hrf_f : rf ∈ fs := (List.mem_filter.mp hrf).1
                    have hrk_eq : rowKey groupKeys (Row.merge rf rd) = rowKey groupKeys rd := by
                      apply hrk_merge
                      intro c hc
                      apply row_none_of_not_in_dom hrf_f
                      intro hm_f
                      exact hdisj_fd c hm_f (hgk_dim c hc)
                    rw [← hrk_eq]
                    apply List.mem_map.mpr
                    refine ⟨Row.merge rf rd, ?_, rfl⟩
                    simp only [origDimJoin, List.mem_flatMap]
                    refine ⟨rd, hrd, ?_⟩
                    rw [hfact_match_eq rd hrd, hrm]
                    exact List.mem_map.mpr ⟨rf, hrf, rfl⟩
            have hkeys_iff_pre : ∀ k,
                (k ∈ preDimJoin.map (rowKey groupKeys)) ↔
                (∃ rd ∈ ds, rdMatches rd = true ∧ rowKey groupKeys rd = k) := by
              intro k
              constructor
              · intro hk
                rcases List.mem_map.mp hk with ⟨m, hm, rfl⟩
                simp only [preDimJoin, List.mem_flatMap] at hm
                rcases hm with ⟨rd, hrd, hm_rd⟩
                rw [hpre_match_eq rd hrd] at hm_rd
                cases hrm : rdMatchKey rd with
                | none => rw [hrm] at hm_rd; simp at hm_rd
                | some v =>
                  rw [hrm] at hm_rd
                  by_cases hmem_ks : [v] ∈ ks_f
                  · simp only [hmem_ks, if_true, List.mem_singleton] at hm_rd
                    subst hm_rd
                    have hrk_eq : rowKey groupKeys (Row.merge (preRow v) rd) = rowKey groupKeys rd := by
                      apply hrk_merge
                      intro c hc
                      apply (hpre_vals v).2.2
                      · intro he; exact hdisj_fd factJoinCol hfj_in_f (he ▸ hgk_dim c hc)
                      · intro he; exact hpa_disj_dim c he (hgk_dim c hc)
                    refine ⟨rd, hrd, ?_, hrk_eq.symm⟩
                    simp only [rdMatches, hrm, decide_eq_true_eq]
                    exact hmem_ks
                  · simp [hmem_ks] at hm_rd
              · rintro ⟨rd, hrd, hmatch, rfl⟩
                simp only [rdMatches] at hmatch
                cases hrm : rdMatchKey rd with
                | none => rw [hrm] at hmatch; simp at hmatch
                | some v =>
                  rw [hrm] at hmatch
                  simp only [decide_eq_true_eq] at hmatch
                  have hrk_eq : rowKey groupKeys (Row.merge (preRow v) rd) = rowKey groupKeys rd := by
                    apply hrk_merge
                    intro c hc
                    apply (hpre_vals v).2.2
                    · intro he; exact hdisj_fd factJoinCol hfj_in_f (he ▸ hgk_dim c hc)
                    · intro he; exact hpa_disj_dim c he (hgk_dim c hc)
                  rw [← hrk_eq]
                  apply List.mem_map.mpr
                  refine ⟨Row.merge (preRow v) rd, ?_, rfl⟩
                  simp only [preDimJoin, List.mem_flatMap]
                  refine ⟨rd, hrd, ?_⟩
                  rw [hpre_match_eq rd hrd, hrm]
                  simp [hmatch]
            -- よってキーリストは Perm
            have hks_perm : (dedup (preDimJoin.map (rowKey groupKeys))).Perm
                (dedup (origDimJoin.map (rowKey groupKeys))) := by
              apply perm_of_nodup_mem_iff (nodup_dedup _) (nodup_dedup _)
              intro k
              rw [mem_dedup, mem_dedup, hkeys_iff_pre, hkeys_iff]
            -- 各 k ∈ dedup (preDimJoin.map ...) に対して buildGroupRow が完全一致することを示す
            have hbuild_eq : ∀ k ∈ dedup (preDimJoin.map (rowKey groupKeys)),
                buildGroupRow groupKeys postAggs k (preDimJoin.filter fun r => rowKey groupKeys r == k) =
                buildGroupRow groupKeys aggs k (origDimJoin.filter fun r => rowKey groupKeys r == k) := by
              intro k hk
              have hk' := (hkeys_iff_pre k).mp (mem_dedup.mp hk)
              let ds_k := ds.filter (fun rd => rdMatches rd && (rowKey groupKeys rd == k))
              have hds_k_ne : ds_k ≠ [] := by
                rcases hk' with ⟨rd, hrd, hrm, hrk⟩
                intro hnil
                have : rd ∈ ds_k := List.mem_filter.mpr ⟨hrd, by simp [hrm, hrk]⟩
                rw [hnil] at this
                cases this
              -- orig 側の filter を ds_k の flatMap へ変換
              have horig_grp :
                  (origDimJoin.filter fun r => rowKey groupKeys r == k) =
                  ds_k.flatMap (fun rd =>
                    match rdMatchKey rd with
                    | none => []
                    | some v => (preGroup v).map fun rf => Row.merge rf rd) := by
                simp only [origDimJoin, filter_flatMap]
                have hgen : ∀ (dl : List Row), (∀ rd ∈ dl, rd ∈ ds) →
                    (dl.flatMap fun rd =>
                      (fs.filterMap fun rf =>
                        let m := Row.merge rf rd
                        if (evalPred m cond).isTrue then some m else none).filter fun r =>
                          rowKey groupKeys r == k) =
                    ((dl.filter fun rd => rdMatches rd && (rowKey groupKeys rd == k)).flatMap fun rd =>
                      match rdMatchKey rd with
                      | none => []
                      | some v => (preGroup v).map fun rf => Row.merge rf rd) := by
                  intro dl hdl
                  induction dl with
                  | nil => rfl
                  | cons rd rds ih =>
                    have hrd := hdl rd (List.mem_cons_self ..)
                    have ih' := ih (fun z hz => hdl z (List.mem_cons_of_mem rd hz))
                    simp only [List.flatMap_cons, List.filter_cons, ih']
                    rw [hfact_match_eq rd hrd]
                    cases hrm : rdMatchKey rd with
                    | none =>
                      simp [rdMatches, hrm]
                    | some v =>
                      have hlist_eq :
                          ((preGroup v).map (fun rf => Row.merge rf rd)).filter (fun r => rowKey groupKeys r == k) =
                          if (rowKey groupKeys rd == k) then (preGroup v).map (fun rf => Row.merge rf rd) else [] := by
                        have hsub : ∀ rf ∈ preGroup v, rowKey groupKeys (Row.merge rf rd) = rowKey groupKeys rd := by
                          intro rf hrf
                          have hrf_f : rf ∈ fs := (List.mem_filter.mp hrf).1
                          apply hrk_merge
                          intro c hc
                          exact row_none_of_not_in_dom hrf_f (fun hm => hdisj_fd c hm (hgk_dim c hc))
                        have hgen_pg : ∀ (fl : List Row), (∀ rf ∈ fl, rowKey groupKeys (Row.merge rf rd) = rowKey groupKeys rd) →
                            (fl.map (fun rf => Row.merge rf rd)).filter (fun r => rowKey groupKeys r == k) =
                            if (rowKey groupKeys rd == k) then fl.map (fun rf => Row.merge rf rd) else [] := by
                          intro fl hfl
                          induction fl with
                          | nil => cases (rowKey groupKeys rd == k) <;> rfl
                          | cons rf rfs ihr =>
                            simp only [List.map_cons, List.filter_cons, hfl rf (List.mem_cons_self ..)]
                            have ihr' := ihr (fun z hz => hfl z (List.mem_cons_of_mem rf hz))
                            cases hcb : (rowKey groupKeys rd == k)
                            · simp only [Bool.false_eq_true, if_false]
                              rw [ihr', hcb]
                              simp
                            · simp only [if_true]
                              rw [ihr', hcb]
                              simp
                        exact hgen_pg (preGroup v) hsub
                      rw [hlist_eq]
                      by_cases hmem_ks : [v] ∈ ks_f
                      · simp only [rdMatches, hrm, hmem_ks]
                        cases (rowKey groupKeys rd == k) <;> simp [hrm]
                      · have hpg_nil : preGroup v = [] := by
                          cases hg : preGroup v with
                          | nil => rfl
                          | cons rf _ =>
                            have hmem := (hpreGroup_nonempty_iff v).mpr (by rw [hg]; simp)
                            exact False.elim (hmem_ks hmem)
                        simp [rdMatches, hrm, hmem_ks, hpg_nil]
                exact hgen ds (fun _ hx => hx)
              -- pre 側の filter を ds_k の map へ変換
              have hpre_grp :
                  (preDimJoin.filter fun r => rowKey groupKeys r == k) =
                  ds_k.map (fun rd =>
                    match rdMatchKey rd with
                    | none => Row.empty
                    | some v => Row.merge (preRow v) rd) := by
                simp only [preDimJoin, filter_flatMap]
                have hgen : ∀ (dl : List Row), (∀ rd ∈ dl, rd ∈ ds) →
                    (dl.flatMap fun rd =>
                      ((eval db preFact).filterMap fun rp =>
                        let m := Row.merge rp rd
                        if (evalPred m cond).isTrue then some m else none).filter fun r =>
                          rowKey groupKeys r == k) =
                    ((dl.filter fun rd => rdMatches rd && (rowKey groupKeys rd == k)).map fun rd =>
                      match rdMatchKey rd with
                      | none => Row.empty
                      | some v => Row.merge (preRow v) rd) := by
                  intro dl hdl
                  induction dl with
                  | nil => rfl
                  | cons rd rds ih =>
                    have hrd := hdl rd (List.mem_cons_self ..)
                    have ih' := ih (fun z hz => hdl z (List.mem_cons_of_mem rd hz))
                    simp only [List.flatMap_cons, List.filter_cons, ih']
                    rw [hpre_match_eq rd hrd]
                    cases hrm : rdMatchKey rd with
                    | none => simp [rdMatches, hrm]
                    | some v =>
                      by_cases hmem_ks : [v] ∈ ks_f
                      · simp only [rdMatches, hrm, hmem_ks, if_true]
                        have hrk_eq : rowKey groupKeys (Row.merge (preRow v) rd) = rowKey groupKeys rd := by
                          apply hrk_merge
                          intro c hc
                          apply (hpre_vals v).2.2
                          · intro he; exact hdisj_fd factJoinCol hfj_in_f (he ▸ hgk_dim c hc)
                          · intro he; exact hpa_disj_dim c he (hgk_dim c hc)
                        simp only [List.filter_cons, hrk_eq]
                        cases (rowKey groupKeys rd == k) <;> simp [hrm]
                      · simp [rdMatches, hrm, hmem_ks]
                exact hgen ds (fun _ hx => hx)
              -- parts の構築 (ds_k 上の各要素 (rd, grp))
              let parts : List (Row × List Row) := ds_k.map fun rd =>
                (rd, match rdMatchKey rd with | none => [] | some v => preGroup v)
              have hparts_ne : parts ≠ [] := by
                cases hds : ds_k with
                | nil => exact False.elim (hds_k_ne hds)
                | cons _ _ => simp [parts, hds]
              have horig_as_pairs :
                  (origDimJoin.filter fun r => rowKey groupKeys r == k) =
                  ((parts.flatMap fun p => p.2.map fun rf => (p.1, rf)).map fun pr => Row.merge pr.2 pr.1) := by
                rw [horig_grp]
                have hgen_p : ∀ (dl : List Row),
                    (dl.flatMap fun rd =>
                      match rdMatchKey rd with
                      | none => []
                      | some v => (preGroup v).map fun rf => Row.merge rf rd) =
                    (((dl.map fun rd => (rd, match rdMatchKey rd with | none => [] | some v => preGroup v)).flatMap
                      fun p => p.2.map fun rf => (p.1, rf)).map fun pr => Row.merge pr.2 pr.1) := by
                  intro dl
                  induction dl with
                  | nil => rfl
                  | cons rd rds ih =>
                    simp only [List.flatMap_cons, List.map_cons, List.map_append, ih]
                    cases rdMatchKey rd with
                    | none => rfl
                    | some v =>
                      simp only [List.map_map, Function.comp_def]
                exact hgen_p ds_k
              have hparts_snd :
                  ((parts.flatMap fun p => p.2.map fun rf => (p.1, rf)).map Prod.snd) =
                  parts.flatMap Prod.snd := by
                have hgen_s : ∀ (ps0 : List (Row × List Row)),
                    ((ps0.flatMap fun p => p.2.map fun rf => (p.1, rf)).map Prod.snd) =
                    ps0.flatMap Prod.snd := by
                  intro ps0
                  induction ps0 with
                  | nil => rfl
                  | cons p ps ih =>
                    simp only [List.flatMap_cons, List.map_append, ih, List.map_map, Function.comp_def, List.map_id']
                exact hgen_s parts
              have hpre_as_parts :
                  (preDimJoin.filter fun r => rowKey groupKeys r == k) =
                  parts.map (fun bg =>
                    match rdMatchKey bg.1 with
                    | none => Row.empty
                    | some v => Row.merge (preRow v) bg.1) := by
                rw [hpre_grp]
                simp only [parts, List.map_map, Function.comp_def]
              -- buildGroupRow の各 agg 項目が一致することを示す
              simp only [buildGroupRow]
              congr 1
              congr 1
              have haggs_eq :
                  (postAggs.map fun a => (a.alias, evalAgg a.op (preDimJoin.filter fun r => rowKey groupKeys r == k))) =
                  (aggs.map fun a => (a.alias, evalAgg a.op (origDimJoin.filter fun r => rowKey groupKeys r == k))) := by
                have hgen_agg : ∀ (as : List AggItem) (idx : Nat),
                    (∀ a ∈ as, isDecomposableAgg (queryCols fact) a = true) →
                    (∀ j (hj : j < as.length),
                      ∀ (v : Val), (preRow v) (preAlias (idx + j)) =
                        some (evalAgg (toPreAgg (as[j]'hj) (idx + j)).op (preGroup v))) →
                    (∀ j (hj : j < as.length), preAlias (idx + j) ∉ queryCols dim) →
                    (mkPostAggs as idx).map (fun a => (a.alias, evalAgg a.op (preDimJoin.filter fun r => rowKey groupKeys r == k))) =
                    as.map (fun a => (a.alias, evalAgg a.op (origDimJoin.filter fun r => rowKey groupKeys r == k))) := by
                  intro as idx hdec hpre_at hnot_dim
                  induction as generalizing idx with
                  | nil => rfl
                  | cons a rest ih =>
                    have ha_dec := hdec a (List.mem_cons_self ..)
                    have hrest_dec : ∀ a' ∈ rest, isDecomposableAgg (queryCols fact) a' = true :=
                      fun a' ha' => hdec a' (List.mem_cons_of_mem a ha')
                    simp only [mkPostAggs, List.map_cons]
                    congr 1
                    · simp only [toPostAgg]
                      congr 1
                      rw [hpre_as_parts, horig_as_pairs]
                      have hrhs_eq :
                          evalAgg a.op ((parts.flatMap fun p => p.2.map fun rf => (p.1, rf)).map fun pr => Row.merge pr.2 pr.1) =
                          evalAgg a.op (parts.flatMap Prod.snd) := by
                        rw [← hparts_snd]
                        apply evalAgg_map_congr_on
                        intro c hc pr hpr
                        rcases List.mem_flatMap.mp hpr with ⟨⟨rd, grp⟩, hpart_mem, hrf_mem⟩
                        rcases List.mem_map.mp hrf_mem with ⟨rf, hrf, rfl⟩
                        have hrd_dsk : rd ∈ ds_k := by
                          rcases List.mem_map.mp hpart_mem with ⟨rd0, hrd0, hpair⟩
                          cases hpair
                          exact hrd0
                        have hrd_ds : rd ∈ ds := (List.mem_filter.mp hrd_dsk).1
                        have hc_in_f : c ∈ queryCols fact := isDecomposableAgg_col_in ha_dec hc
                        have hc_not_d : c ∉ queryCols dim := hdisj_fd c hc_in_f
                        simp only [Row.getVal]
                        rw [Row.merge_eq_left_of_not_right (row_none_of_not_in_dom hrd_ds hc_not_d)]
                      rw [hrhs_eq]
                      apply evalAgg_two_stage parts hparts_ne
                        (fun rd _ => match rdMatchKey rd with | none => Row.empty | some v => Row.merge (preRow v) rd)
                        a idx
                      · rcases a with ⟨op, al⟩
                        cases op <;> simp [isDecomposableAgg] at ha_dec ⊢
                      · intro rd grp hmem_p
                        rcases List.mem_map.mp hmem_p with ⟨rd0, hrd0, hpair⟩
                        have hrd_eq : rd = rd0 := congrArg Prod.fst hpair |>.symm
                        subst hrd_eq
                        have hrd_ds : rd ∈ ds := (List.mem_filter.mp hrd0).1
                        have hrm_t : rdMatches rd = true := by
                          have hb := (List.mem_filter.mp hrd0).2
                          simp only [Bool.and_eq_true] at hb
                          exact hb.1
                        simp only [rdMatches] at hrm_t
                        cases hrm : rdMatchKey rd with
                        | none => rw [hrm] at hrm_t; simp at hrm_t
                        | some v =>
                          have hpa_not_d : preAlias idx ∉ queryCols dim := by
                            have := hnot_dim 0 (by simp)
                            simpa using this
                          have hrd_none : rd (preAlias idx) = none := row_none_of_not_in_dom hrd_ds hpa_not_d
                          simp only [Row.getVal, Row.merge_eq_left_of_not_right hrd_none]
                          have hpre_eq := hpre_at 0 (by simp) v
                          simp only [Nat.add_zero, List.getElem_cons_zero] at hpre_eq
                          rw [hpre_eq]
                          have hgrp_eq : grp = preGroup v := by
                            have hsnd := congrArg Prod.snd hpair
                            dsimp only at hsnd
                            rw [hrm] at hsnd
                            exact hsnd.symm
                          rw [hgrp_eq]
                          rfl
                    · apply ih (idx + 1) hrest_dec
                      · intro j hj v
                        have h := hpre_at (j + 1) (by simp; omega) v
                        have heq : idx + 1 + j = idx + (j + 1) := by omega
                        rw [heq]
                        exact h
                      · intro j hj
                        have h := hnot_dim (j + 1) (by simp; omega)
                        have heq : idx + 1 + j = idx + (j + 1) := by omega
                        rw [heq]
                        exact h
                exact hgen_agg aggs 0 haggs_dec (fun j hj v => (hpre_vals v).2.1 j hj)
                  (fun j hj hm => hpa_disj_dim (preAlias (0 + j)) (mem_preAliasList aggs 0 j hj) hm)
              rw [haggs_eq]
            -- 最終的な Perm 合成
            have hmid :
                ((dedup (preDimJoin.map (rowKey groupKeys))).map fun k =>
                  buildGroupRow groupKeys postAggs k (preDimJoin.filter fun r => rowKey groupKeys r == k)).Perm
                ((dedup (origDimJoin.map (rowKey groupKeys))).map fun k =>
                  buildGroupRow groupKeys aggs k (origDimJoin.filter fun r => rowKey groupKeys r == k)) := by
              have h2 :
                  ((dedup (preDimJoin.map (rowKey groupKeys))).map fun k =>
                    buildGroupRow groupKeys postAggs k (preDimJoin.filter fun r => rowKey groupKeys r == k)) =
                  ((dedup (preDimJoin.map (rowKey groupKeys))).map fun k =>
                    buildGroupRow groupKeys aggs k (origDimJoin.filter fun r => rowKey groupKeys r == k)) := by
                apply List.map_congr_left
                exact hbuild_eq
              rw [h2]
              exact hks_perm.map _
            exact (hpre_gb.trans hmid).trans horig_gb.symm
          · cases h
      | _ => simp at h
    | _ => simp at h

def perfRules : List VerifiedRule :=
  [ elimRedundantFKJoinRule
  , decorrelateScalarAggSubqueryRule
  , eagerAggThroughJoinRule
  , splitOrToUnionAllRule
  ]

def allRules : List VerifiedRule :=
  baseRules ++ perfRules

end LeanSqlOpt
