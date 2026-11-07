import Mahlo.FS.Seq
import Mahlo.FS.Arith

/-! 解析 `info` の基本性質、共終数の分類（後者・0）と、FS の 0・後者・自然数の公理。 -/

namespace MahloOCF.FS

open Tm

/-! ### 解析 `info` の基本性質 -/

/-- 崩壊 `Ψ_π(X)` の列の記述 -/
def cs (π X : Tm) : SeqD := cseq π (info π).fam X (info X).sums

theorem info_seq_psi (π X : Tm) : (info (Psi π X)).seq = cs π X := rfl

theorem info_fam_xi (m : Nat) (q : Tm) : (info (Xi m q)).fam = .xi m q (info q).sums := rfl

theorem info_fam_om (c : Tm) : (info (Om c)).fam = .om := rfl

theorem dom_zero : dom zero = .zero := rfl
theorem dom_M (m : Nat) : dom (M m) = .big (M m) := rfl
theorem dom_plus (a b : Tm) : dom (plus a b) = dom b := rfl
theorem dom_xi (m : Nat) (q : Tm) : dom (Xi m q) = .big (Xi m q) := rfl

/-- `Ω_c` は `c = 0` か後者なら正則、そうでなければ `c` と同じ共終数 -/
def omReg (c : Tm) : Prop := c = zero ∨ isSucc c = true

instance (c : Tm) : Decidable (omReg c) := inferInstanceAs (Decidable (c = zero ∨ isSucc c = true))

theorem info_seq_om (c : Tm) :
    (info (Om c)).seq = if omReg c then .reg (Om c) (base (Om c)) else .om (info c).seq := by
  by_cases h : omReg c
  · rw [if_pos h]; simp only [info]; rw [if_pos (show c = zero ∨ isSucc c = true from h)]
  · rw [if_neg h]; simp only [info]; rw [if_neg (show ¬(c = zero ∨ isSucc c = true) from h)]

theorem dom_om (c : Tm) : dom (Om c) = if omReg c then .big (Om c) else dom c := by
  unfold dom
  rw [info_seq_om]
  split <;> rfl

theorem dom_psi (π X : Tm) : dom (Psi π X) = (cs π X).dom := rfl

theorem fundBig_plus (a b ξ : Tm) : fundBig (plus a b) ξ = oadd a (fundBig b ξ) := rfl
theorem fundBig_M (m : Nat) (ξ : Tm) : fundBig (M m) ξ = oadd (base (M m)) ξ := rfl
theorem fundBig_xi (m : Nat) (q ξ : Tm) : fundBig (Xi m q) ξ = oadd (base (Xi m q)) ξ := rfl

theorem fundBig_om (c ξ : Tm) :
    fundBig (Om c) ξ = if omReg c then oadd (base (Om c)) ξ else Om (sc (fundBig c ξ)) := by
  unfold fundBig
  rw [info_seq_om]
  split <;> rfl

theorem fundBig_psi (π X ξ : Tm) : fundBig (Psi π X) ξ = (cs π X).big ξ := rfl

theorem fundNat_plus (a b : Tm) (n : Nat) : fundNat (plus a b) n = oadd a (fundNat b n) := rfl

theorem fundNat_om {c : Tm} (hc : ¬ omReg c) (n : Nat) :
    fundNat (Om c) n = Om (sc (fundNat c n)) := by
  unfold fundNat
  rw [info_seq_om, if_neg hc]
  rfl

theorem fundNat_psi (π X : Tm) (n : Nat) : fundNat (Psi π X) n = (cs π X).nat n := rfl

theorem fund_eq (t ξ : Tm) : fund t ξ =
    match dom t with
    | .zero => zero
    | .one => pred t
    | .omega => fundNat t (natOf ξ)
    | .big σ => fundBig t (if ltB ξ σ then ξ else zero) := rfl

/-- 加数の記述は各加数の記述 -/
def Coh (l : DL) : Prop := ∀ p ∈ l, p.2 = (info p.1).seq

theorem info_sums_fst : ∀ t : Tm, (info t).sums.map Prod.fst = summands t
  | .plus a b => by
    show a :: (info b).sums.map Prod.fst = a :: summands b
    rw [info_sums_fst b]
  | .zero | .M _ | .Om _ | .Xi _ _ | .Psi _ _ => rfl

theorem coh_sums : ∀ t : Tm, Coh (info t).sums
  | .plus a b => by
    intro p hp
    rcases List.mem_cons.mp hp with rfl | hp
    · rfl
    · exact coh_sums b p hp
  | .zero => by intro p hp; cases hp
  | .M _ | .Om _ | .Xi _ _ | .Psi _ _ => by
    intro p hp
    rcases List.mem_singleton.mp hp with rfl
    rfl

theorem preT_info (X : Tm) : preT (info X).sums = (summands X).dropLast := by
  rw [preT, List.map_dropLast, info_sums_fst]

theorem lastT_info (X : Tm) : lastT (info X).sums = (summands X).getLast?.getD zero := by
  rw [lastT, ← List.getLast?_map, info_sums_fst]

theorem lastS_coh {l : DL} (h : Coh l) : lastS l = (info (lastT l)).seq := by
  unfold lastS lastT
  cases e : l.getLast? with
  | none => rfl
  | some p => exact h p (List.mem_of_getLast? e)

/-! ### 後者 -/

theorem isSucc_principal {x : Tm} (hx : isPrincipal x = true) : isSucc x = (x == one) := by
  simp only [isSucc, summands_principal hx, List.getLast?_singleton, Option.some_beq_some]

theorem isSucc_plus {a b : Tm} (hb : b ≠ zero) : isSucc (plus a b) = isSucc b := by
  obtain ⟨h', t', e⟩ := List.exists_cons_of_ne_nil (summands_ne_nil hb)
  simp only [isSucc, summands_plus, e, List.getLast?_cons_cons]

theorem summands_eq_dropLast_one {a : Tm} (hs : isSucc a = true) :
    summands a = (summands a).dropLast ++ [one] := by
  have h : (summands a).getLast? = some one := by simpa [isSucc] using hs
  obtain ⟨ys, hys⟩ := List.getLast?_eq_some_iff.mp h
  rw [hys, List.dropLast_concat]

theorem wnf_pred {a : Tm} (ha : WNF a) : WNF (pred a) := by
  unfold pred
  apply wnf_ofSummands
  have e : (summands a).dropLast ++ (summands a).drop ((summands a).length - 1) = summands a := by
    rw [List.dropLast_eq_take, List.take_append_drop]
  have h := nfl_summands ha
  rw [← e] at h
  exact nfl_append_left h

/-- 後者 `a` は `pred a + 1` -/
theorem succT_pred {a : Tm} (ha : WNF a) (hs : isSucc a = true) : succT (pred a) = a := by
  have e := summands_eq_dropLast_one hs
  have hp := nfl_principal (nfl_summands ha)
  have h1 : summands (succT (pred a)) = summands a := by
    rw [summands_succT, pred, summands_ofSummands _ (fun x hx => hp x (List.dropLast_subset _ hx))]
    exact e.symm
  calc succT (pred a) = ofSummands (summands (succT (pred a))) :=
        (ofSummands_summands _ (succT_WNF (wnf_pred ha))).symm
    _ = ofSummands (summands a) := by rw [h1]
    _ = a := ofSummands_summands a ha

theorem pred_lt {a : Tm} (ha : WNF a) (hs : isSucc a = true) : Lt (pred a) a := by
  have := lt_succT (pred a)
  rwa [succT_pred ha hs] at this

theorem le_pred {a x : Tm} (ha : WNF a) (hs : isSucc a = true) (hx : WNF x) (h : Lt x a) :
    Le x (pred a) := by
  have hpF := wnf_pred ha
  rcases triY hx hpF with h1 | h1 | h1
  · exact Or.inr h1
  · exact Or.inl h1
  · exfalso
    have h2 : Le (succT (pred a)) x := succT_leY hpF hx h1
    rw [succT_pred ha hs] at h2
    exact not_lt_of_leY ha hx h2 h

theorem pred_eq_predT (a : Tm) : pred a = predT a := rfl

end MahloOCF.FS

/-! ### 崩壊の列の記述の形 -/

namespace MahloOCF.FS

open Tm

/-- 崩壊の列の記述の形（`none`・`one`・`mul`・`tower`・`app`、一つずらした `app`） -/
def SeqD.isC : SeqD → Bool
  | .none | .one | .mul _ _ | .tower _ | .app _ _ _ _ _ _ _ => true
  | .shift (.app _ _ _ _ _ _ _) => true
  | _ => false

theorem SeqD.app_dom_ne (τ : Tm) (g : Gen) (pre : List Tm) (R : Tm) (r : SeqD) (P c : Tm) :
    (SeqD.app τ g pre R r P c).dom ≠ .one ∧ (SeqD.app τ g pre R r P c).dom ≠ .zero := by
  simp only [SeqD.dom]
  split
  · split <;> simp
  · simp

/-- 崩壊の列の記述の共終数が後者なら、記述は `one` -/
theorem SeqD.eq_one_of_dom {s : SeqD} (h : s.isC = true) (hd : s.dom = .one) : s = .one := by
  cases s with
  | app τ g pre R r P c => exact absurd hd (SeqD.app_dom_ne _ _ _ _ _ _ _).1
  | shift s =>
    cases s with
    | app τ g pre R r P c => exact absurd hd (SeqD.app_dom_ne τ g pre R r P c).1
    | _ => simp [isC] at h
  | _ => simp_all [isC, SeqD.dom]

theorem SeqD.eq_none_of_dom {s : SeqD} (h : s.isC = true) (hd : s.dom = .zero) : s = .none := by
  cases s with
  | app τ g pre R r P c => exact absurd hd (SeqD.app_dom_ne _ _ _ _ _ _ _).2
  | shift s =>
    cases s with
    | app τ g pre R r P c => exact absurd hd (SeqD.app_dom_ne τ g pre R r P c).2
    | _ => simp [isC] at h
  | _ => simp_all [isC, SeqD.dom]

/-- `mkApp` が作るのは `app`（調整 `c` だけが変わりうる） -/
theorem mkApp_eq_some {ceil : Tm} {g : Gen} {pre : List Tm} {R : Tm} {r : SeqD} {P c : Tm} {s : SeqD}
    (h : mkApp ceil g pre R r P c = some s) : ∃ c', s = .app ceil g pre R r P c' := by
  unfold mkApp at h
  dsimp only at h
  split at h
  · cases h
  · split at h
    · split at h
      · cases h; exact ⟨_, rfl⟩
      · split at h
        · cases h
        · split at h
          · cases h; exact ⟨_, rfl⟩
          · cases h; exact ⟨_, rfl⟩
    · cases h; exact ⟨_, rfl⟩

theorem mkApp_isC {ceil : Tm} {g : Gen} {pre : List Tm} {R : Tm} {r : SeqD} {P c : Tm} {s : SeqD}
    (h : mkApp ceil g pre R r P c = some s) : s.isC = true ∧ s ≠ .none := by
  obtain ⟨c', rfl⟩ := mkApp_eq_some h
  exact ⟨rfl, fun e => by cases e⟩

theorem mkApp_ne_none {ceil : Tm} {g : Gen} {pre : List Tm} {R : Tm} {r : SeqD} {P c : Tm} {s : SeqD}
    (h : mkApp ceil g pre R r P c = some s) : s ≠ .none := (mkApp_isC h).2

theorem getD_isC {o : Option SeqD} (h : ∀ s, o = some s → s.isC = true) : (o.getD .none).isC = true := by
  cases o with
  | none => rfl
  | some s => exact h s rfl

theorem mahloVK_isC (m : Nat) (q : Tm) (qs : DL) (ceil : Tm) (P : Option Tm) :
    (mahloVK m q qs ceil P).isC = true := by
  unfold mahloVK
  dsimp only
  repeat' split
  all_goals first | exact (mkApp_isC (by assumption)).1 | rfl

theorem famSeq_isC : ∀ (πf : Fam) (ceil : Tm) (P : Option Tm), (famSeq πf ceil P).isC = true
  | .om, _, P => by unfold famSeq; cases P <;> rfl
  | .xi m q qs, ceil, P => by unfold famSeq; exact mahloVK_isC _ _ _ _ _
  | .none, _, _ => by unfold famSeq; rfl

theorem insertAtL_isC (τ : Tm) (τf : Fam) (c p : Tm) (ys : DL) : (insertAtL τ τf c p ys).isC = true := by
  unfold insertAtL
  repeat' split
  all_goals first | exact famSeq_isC _ _ _ | exact (mkApp_isC (by assumption)).1

theorem limitSeq_isC (τ : Tm) (τf : Fam) (c X : Tm) (xs : DL) : (limitSeq τ τf c X xs).isC = true := by
  unfold limitSeq
  dsimp only
  repeat' split
  all_goals first
    | exact insertAtL_isC _ _ _ _ _
    | exact getD_isC (fun s hs => (mkApp_isC hs).1)

theorem cseq_isC (π : Tm) (πf : Fam) (X : Tm) (xs : DL) : (cseq π πf X xs).isC = true := by
  unfold cseq
  repeat' split
  all_goals first
    | rfl
    | exact famSeq_isC _ _ _
    | exact limitSeq_isC _ _ _ _ _

theorem cs_isC (π X : Tm) : (cs π X).isC = true := cseq_isC _ _ _ _

end MahloOCF.FS

/-! ### 共終数が 0・後者になる項 -/

namespace MahloOCF.FS

open Tm

theorem cmpList_prefix : ∀ (l m m' : List Tm), cmpList (l ++ m) (l ++ m') = cmpList m m'
  | [], _, _ => rfl
  | x :: xs, m, m' => by
    rw [List.cons_append, List.cons_append, cmpList_cons_cons_eq _ _ (cmpP_self x)]
    exact cmpList_prefix xs m m'

/-- 標準形の `Ψ_π(X)` では、目標の引数 `r` は `X` 未満 -/
theorem lt_argR {π X r : Tm} (hP : PsiNF π X) (hr : argR? π = some r) : Lt r X := by
  cases π with
  | Xi m q =>
    simp only [argR?, Option.some.injEq] at hr; subst hr
    exact hP.act m q rfl
  | _ => simp [argR?] at hr

theorem wnf_argR {π r : Tm} (hπ : WNF π) (hr : argR? π = some r) : WNF r := by
  cases π with
  | Xi m q => simp only [argR?, Option.some.injEq] at hr; subst hr; exact hπ.xi.2.1
  | _ => simp [argR?] at hr

/-- 標準形の `Ψ_π(X)`（`X` は 0 でない）では、`X` の最後の加数は `r` の対応する残りより大きい -/
theorem lt_tailRaw {π X rt : Tm} (hX : WNF X) (hX0 : X ≠ zero) (hP : PsiNF π X)
    (h : tailRaw (argR? π) (summands X).dropLast = some rt) :
    Lt rt ((summands X).getLast?.getD zero) := by
  cases hr : argR? π with
  | none => rw [hr] at h; simp [tailRaw] at h
  | some r =>
    rw [hr] at h
    have hrX := lt_argR hP hr
    have hrW := wnf_argR hP.piF hr
    simp only [tailRaw] at h
    split at h
    · rename_i hpre
      simp only [Option.some.injEq] at h
      subst h
      have hne := summands_ne_nil hX0
      have eX : summands X = (summands X).dropLast ++ [(summands X).getLast hne] :=
        (List.dropLast_concat_getLast hne).symm
      have eL : (summands X).getLast?.getD zero = (summands X).getLast hne := by
        rw [List.getLast?_eq_some_getLast hne]; rfl
      rw [eL]
      have er : summands r = (summands X).dropLast ++ (summands r).drop (summands X).dropLast.length := by
        have := (List.take_append_drop (summands X).dropLast.length (summands r)).symm
        rw [hpre.2] at this
        exact this
      have hRmem : (summands X).getLast hne ∈ summands X := List.getLast_mem hne
      have hRp := nfl_principal (nfl_summands hX) _ hRmem
      have hDp : ∀ x, x ∈ (summands r).drop (summands X).dropLast.length → isPrincipal x = true :=
        fun x hx => nfl_principal (nfl_summands hrW) x (List.mem_of_mem_drop hx)
      show cmp _ _ = .lt
      rw [cmp_eq, summands_ofSummands _ hDp, summands_principal hRp]
      calc cmpList (List.drop (summands X).dropLast.length (summands r)) [(summands X).getLast hne]
          = cmpList ((summands X).dropLast ++ List.drop (summands X).dropLast.length (summands r))
              ((summands X).dropLast ++ [(summands X).getLast hne]) := (cmpList_prefix _ _ _).symm
        _ = cmpList (summands r) (summands X) := by rw [← er, ← eX]
        _ = .lt := by have := hrX; unfold Lt at this; rw [cmp_eq] at this; exact this
    · cases h

theorem wnf_tailRaw {r rt : Tm} {pre : List Tm} (hr : WNF r) (h : tailRaw (some r) pre = some rt) :
    WNF rt := by
  simp only [tailRaw] at h
  split at h
  · simp only [Option.some.injEq] at h
    subst h
    apply wnf_ofSummands
    have e := (List.take_append_drop pre.length (summands r)).symm
    have hn := nfl_summands hr
    rw [e] at hn
    exact nfl_append_right hn
  · cases h

/-- 標準形の `Ψ_π(X)`（`X ≠ 0`）の素の近似は作れる -/
theorem mkApp_plain_ne_none {π X : Tm} (hX : WNF X) (hX0 : X ≠ zero) (hP : PsiNF π X) (ceil : Tm)
    (r : SeqD) : mkApp ceil (.psi π) (preT (info X).sums) (lastT (info X).sums) r zero zero ≠ none := by
  rw [preT_info, lastT_info]
  unfold mkApp
  simp only [ne_eq, not_true_eq_false, false_and, ↓reduceIte, Gen.tgt?]
  split
  · simp
  · rename_i rt hrt
    have hlt := lt_tailRaw hX hX0 hP hrt
    have hne := summands_ne_nil hX0
    have hRW : WNF ((summands X).getLast?.getD zero) := by
      rw [List.getLast?_eq_some_getLast hne]
      exact ((nfl_summands hX).1 _ (List.getLast_mem hne)).1
    cases hr : argR? π with
    | none => rw [hr] at hrt; simp [tailRaw] at hrt
    | some r =>
      rw [hr] at hrt
      have hrtW := wnf_tailRaw (wnf_argR hP.piF hr) hrt
      have hleB : leB ((summands X).getLast?.getD zero) rt = false := by
        cases e : leB ((summands X).getLast?.getD zero) rt with
        | false => rfl
        | true =>
          exfalso
          have : cmp ((summands X).getLast?.getD zero) rt ≠ .gt := by simpa [leB] using e
          exact not_lt_of_leY hRW hrtW (le_of_ne_gtY hRW hrtW this) hlt
      simp only [hleB, Bool.false_eq_true, ↓reduceIte]
      repeat' split
      all_goals simp

theorem mahloVK_ne_none (m : Nat) (q : Tm) (qs : DL) (ceil : Tm) (P : Option Tm) :
    mahloVK m q qs ceil P ≠ .none := by
  unfold mahloVK
  dsimp only
  repeat' split
  all_goals first | (apply mkApp_ne_none; assumption) | simp

theorem famSeq_some_ne_none (πf : Fam) (hf : πf ≠ .none) (ceil p : Tm) : famSeq πf ceil (some p) ≠ .none := by
  cases πf with
  | om => unfold famSeq; simp
  | xi m q qs => unfold famSeq; exact mahloVK_ne_none _ _ _ _ _
  | none => exact absurd rfl hf

theorem insertAtL_ne_none {τ : Tm} {τf : Fam} (hf : τf ≠ .none) (ceil p : Tm) (ys : DL) :
    insertAtL τ τf ceil p ys ≠ .none := by
  unfold insertAtL
  repeat' split
  all_goals first | exact famSeq_some_ne_none _ hf _ _ | (apply mkApp_ne_none; assumption) | simp

theorem limitSeq_ne_none {τ : Tm} {τf : Fam} (hf : τf ≠ .none) {ceil X : Tm} {xs : DL}
    (hplain : ∀ r, mkApp ceil (.psi τ) (preT xs) (lastT xs) r zero zero ≠ none) :
    limitSeq τ τf ceil X xs ≠ .none := by
  have key : ∀ r, (mkApp ceil (.psi τ) (preT xs) (lastT xs) r zero zero).getD .none ≠ .none := by
    intro r
    obtain ⟨s, hs⟩ := Option.ne_none_iff_exists'.mp (hplain r)
    rw [hs, Option.getD_some]
    exact mkApp_ne_none hs
  unfold limitSeq
  dsimp only
  repeat' split
  all_goals first | exact key _ | exact insertAtL_ne_none hf _ _ _ | simp

theorem info_fam_ne_none {π : Tm} (h : IsTgt π) : (info π).fam ≠ .none := by
  rcases h with rfl | ⟨c, rfl, -⟩ | ⟨n, p, rfl⟩
  · rw [info_fam_om]; simp
  · rw [info_fam_om]; simp
  · rw [info_fam_xi]; simp

/-- 標準形の崩壊 `Ψ_π(X)` の列の記述は空でない -/
theorem cs_ne_none {π X : Tm} (h : WNF (Psi π X)) : cs π X ≠ .none := by
  have hP := h.psi
  have hf := info_fam_ne_none hP.tgt
  unfold cs cseq
  split
  · rename_i hX
    subst hX
    rcases hP.tgt with rfl | ⟨c, rfl, -⟩ | ⟨n, q, rfl⟩
    · simp
    · simp only
      split <;> simp
    · exact absurd (hP.act n q rfl) (not_lt_zero q)
  · rename_i hX0
    split
    · split
      · split <;> simp
      · rename_i hv
        rcases hP.tgt with rfl | ⟨c, rfl, -⟩ | ⟨n, q, rfl⟩
        · simp [validR, argR?] at hv
        · simp [validR, argR?] at hv
        · rw [info_fam_xi]; unfold famSeq; exact mahloVK_ne_none _ _ _ _ _
    · exact limitSeq_ne_none hf (mkApp_plain_ne_none hP.aF hX0 hP π)

end MahloOCF.FS

namespace MahloOCF.FS

open Tm

/-! ### 共終数の分類 -/

theorem mkApp_ne_one {ceil : Tm} {g : Gen} {pre : List Tm} {R : Tm} {r : SeqD} {P c : Tm} {s : SeqD}
    (h : mkApp ceil g pre R r P c = some s) : s ≠ .one := by
  obtain ⟨c', rfl⟩ := mkApp_eq_some h
  intro e; cases e

theorem mahloVK_ne_one (m : Nat) (q : Tm) (qs : DL) (ceil : Tm) (P : Option Tm) :
    mahloVK m q qs ceil P ≠ .one := by
  unfold mahloVK
  dsimp only
  repeat' split
  all_goals first | (apply mkApp_ne_one; assumption) | simp

theorem famSeq_ne_one : ∀ (πf : Fam) (ceil : Tm) (P : Option Tm), famSeq πf ceil P ≠ .one
  | .om, _, P => by unfold famSeq; cases P <;> simp
  | .xi m q qs, ceil, P => by unfold famSeq; exact mahloVK_ne_one _ _ _ _ _
  | .none, _, _ => by unfold famSeq; simp

theorem getD_ne_one {o : Option SeqD} (h : ∀ s, o = some s → s ≠ .one) : o.getD .none ≠ .one := by
  cases o with
  | none => simp
  | some s => exact h s rfl

theorem insertAtL_ne_one (τ : Tm) (τf : Fam) (c p : Tm) (ys : DL) : insertAtL τ τf c p ys ≠ .one := by
  unfold insertAtL
  repeat' split
  all_goals first | exact famSeq_ne_one _ _ _ | (apply mkApp_ne_one; assumption)

theorem limitSeq_ne_one (τ : Tm) (τf : Fam) (c X : Tm) (xs : DL) : limitSeq τ τf c X xs ≠ .one := by
  unfold limitSeq
  dsimp only
  repeat' split
  all_goals first
    | exact insertAtL_ne_one _ _ _ _ _
    | exact getD_ne_one (fun s hs => mkApp_ne_one hs)

/-- 崩壊の列の記述が後者になるのは `Ψ_{Ω_0}(0) = 1` だけ -/
theorem cs_eq_one {π X : Tm} (h : cs π X = .one) : π = Om zero ∧ X = zero := by
  unfold cs cseq at h
  split at h
  · rename_i hX
    split at h
    · rename_i c
      split at h
      · rename_i hc; exact ⟨by rw [hc], hX⟩
      · cases h
    · cases h
  · split at h
    · split at h
      · split at h <;> cases h
      · exact absurd h (famSeq_ne_one _ _ _)
    · exact absurd h (limitSeq_ne_one _ _ _ _ _)

theorem dom_one_iff_psi {π X : Tm} : (cs π X).dom = .one ↔ π = Om zero ∧ X = zero := by
  constructor
  · intro hd
    exact cs_eq_one (SeqD.eq_one_of_dom (cs_isC π X) hd)
  · rintro ⟨rfl, rfl⟩
    rfl

/-- 標準形の項の共終数が後者 ⟺ 最後の加数が `1` -/
theorem dom_eq_one_iff : ∀ {t : Tm}, WNF t → (dom t = .one ↔ isSucc t = true)
  | .zero, _ => by simp [dom_zero, isSucc, summands]
  | .M n, _ => by simp [dom_M, isSucc, summands, one]
  | .plus a b, h => by
    obtain ⟨-, hb, -, hb0⟩ := h.plus
    rw [isSucc_plus hb0, ← dom_eq_one_iff hb, dom_plus]
  | .Om c, h => by
    have hc := h.om.1
    rw [dom_om]
    split
    · simp [isSucc, summands, one]
    · rename_i hcs
      rw [dom_eq_one_iff hc]
      constructor
      · intro h'; exact absurd (Or.inr h') hcs
      · intro h'; simp [isSucc, summands, one] at h'
  | .Xi n a, _ => by simp [dom_xi, isSucc, summands, one]
  | .Psi π X, _ => by
    rw [dom_psi, dom_one_iff_psi, isSucc_principal rfl]
    simp [one]

/-- 標準形の項の共終数が 0 ⟺ 項が 0 -/
theorem dom_eq_zero_iff : ∀ {t : Tm}, WNF t → (dom t = .zero ↔ t = zero)
  | .zero, _ => by simp [dom_zero]
  | .M n, _ => by simp [dom_M]
  | .plus a b, h => by
    obtain ⟨-, hb, -, hb0⟩ := h.plus
    simp only [dom_plus, reduceCtorEq, iff_false]
    rw [dom_eq_zero_iff hb]
    exact hb0
  | .Om c, h => by
    have hc := h.om.1
    simp only [dom_om, reduceCtorEq, iff_false]
    split
    · simp
    · rename_i hcs
      rw [dom_eq_zero_iff hc]
      intro e; exact hcs (Or.inl e)
  | .Xi n a, _ => by simp [dom_xi]
  | .Psi π X, h => by
    simp only [dom_psi, reduceCtorEq, iff_false]
    intro e
    exact cs_ne_none h (SeqD.eq_none_of_dom (cs_isC _ _) e)

theorem fund_of_dom_one {t : Tm} (ξ : Tm) (h : dom t = .one) : fund t ξ = pred t := by
  rw [fund_eq, h]

theorem fund_zero (ξ : Tm) : fund zero ξ = zero := rfl

theorem wnf_ofNatT (n : Nat) : WNF (ofNatT n) := wnf_mulNat WNF.one rfl n

theorem dom_ofNatT (n : Nat) : dom (ofNatT (n + 1)) = .one := by
  rw [dom_eq_one_iff (wnf_ofNatT _)]
  simp only [isSucc, ofNatT, summands_mulNat (x := one) rfl, List.getLast?_replicate]
  simp

theorem fund_ofNatT (n : Nat) (ξ : Tm) : fund (ofNatT (n + 1)) ξ = ofNatT n := by
  rw [fund_of_dom_one ξ (dom_ofNatT n), pred, ofNatT, summands_mulNat rfl, List.dropLast_replicate]
  rfl

end MahloOCF.FS
