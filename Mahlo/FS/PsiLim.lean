import Mahlo.FS.Split

/-! 極限 `X` の崩壊 `Ψ_π(X)` の列のうち、素の近似 `Ψ_π(pre ⊕ (c ⊕ R[ν]))` の場合。

`X = pre + R`（`R` は最後の加数）で、`R` の列が `ω` 型（`inv_psi_lim_nat`）か、共終数 `σ` が `π` 未満の
正則型（`inv_psi_lim_big`）のとき。`c` は有効性の調整（`π = Ξ_m(d)` で `pre` が `d` の先頭部分のとき、
`d < pre ⊕ (c ⊕ R[0])` となるように `d` の残りの先頭部分を足す）。

近似 `y = Ψ_π(A)`（`A = pre ⊕ (c ⊕ x)`、`x = R[ν]`）が標準形であること（`A ∈ C(A, y)`）は次から出る。

* `X` の加数 `s` は `C(X, Ψ_π(X))` に入る。`s` の部分項で `Ψ_π(X)` 未満のものは `y` 未満（移し替え、
  引数の条件 `argCond`）なので、`s ∈ C(A, y)`（`approx_core`）。
* `x ∈ C(A, y)` は `R` の列の上界（`ub`）を `(g, d) = (A, y)` に使う。`y` は切断（`cut_psi`）。
* `c` の加数は `d` の加数で、`d ∈ C(d, Ψ_π(X))`（底の条件）から `d ∈ C(A, y)`。 -/

namespace MahloOCF.FS

open Tm

/-! ### 補題 -/

theorem argR_some {π δ : Tm} (h : argR? π = some δ) : ∃ m, π = .Xi m δ := by
  cases π with
  | Xi m d => simp only [argR?, Option.some.injEq] at h; exact ⟨m, by rw [h]⟩
  | _ => simp [argR?] at h

theorem validR_iff {π A : Tm} : validR π A = true ↔ ∀ δ, argR? π = some δ → Lt δ A := by
  unfold validR
  cases h : argR? π with
  | none => simp
  | some δ => simp [ltB_iff]

theorem combine_psi_zero {π c x : Tm} (pre : List Tm) (hc : WNF c) (hx : WNF x) :
    combine (.psi π) pre c .zero x = oadd (ofSummands pre) (oadd c x) := by
  show oadd (ofSummands pre) (nsum (oadd c x) .zero) = _
  rw [nsum_zero _ (wnf_oadd hc hx)]

theorem isSucc_of_last {X R : Tm} {pre : List Tm} (hsX : summands X = pre ++ [R])
    (hRp : isPrincipal R = true) : isSucc X = isSucc R := by
  rw [isSucc_principal hRp]
  unfold isSucc
  rw [hsX]
  simp

theorem not_isSucc_reg {σ : Tm} (h : IsRegY σ) : ¬ isSucc σ = true := by
  rcases h with rfl | ⟨c, rfl, -⟩ | ⟨n, rfl⟩ | ⟨n, p, rfl⟩ <;> simp [isSucc, summands, one]

theorem one_lt_reg {σ : Tm} (hσ : WNF σ) (h : IsRegY σ) (h0 : Lt .zero σ) : Lt one σ :=
  succT_lt_of_not_succ WNF.zero hσ (not_isSucc_reg h) h0

/-! ### 有効性の調整 -/

/-- 調整 `c` の性質（`c` は目標 `π` の成分から作れる） -/
structure AdjOK (π : Tm) (pre : List Tm) (R x0 c : Tm) : Prop where
  cF : WNF c
  cR : Lt c R
  cC : ∀ g d, WNF g → g ≠ .zero → Cut d → inC π g d = true → ¬ Lt π d → inC c g d = true
  valid : ∀ x, WNF x → Le x0 x → validR π (oadd (ofSummands pre) (oadd c x)) = true

/-- 下限 `δ` が `pre` で始まるとき：`δ = pre ⊕ rt` -/
theorem tailRaw_some {δ rt : Tm} {pre : List Tm} (hδ : WNF δ) (h : tailRaw (some δ) pre = some rt) :
    WNF rt ∧ summands δ = pre ++ summands rt ∧ δ = oadd (ofSummands pre) rt := by
  have hrt := wnf_tailRaw hδ h
  simp only [tailRaw] at h
  split at h
  · rename_i hc
    simp only [Option.some.injEq] at h
    have e := (List.take_append_drop pre.length (summands δ)).symm
    rw [hc.2] at e
    have hn : NFL (pre ++ (summands δ).drop pre.length) := by rw [← e]; exact nfl_summands hδ
    have hsrt : summands rt = (summands δ).drop pre.length := by
      rw [← h]; exact summands_ofSummands _ (nfl_principal (nfl_append_right hn))
    have h1 := summands_oadd_nfl hn
    rw [h] at h1
    exact ⟨hrt, by rw [hsrt]; exact e,
      eq_of_summands_eq hδ (wnf_oadd (wnf_ofSummands (nfl_append_left hn)) hrt) (by rw [h1]; exact e)⟩
  · cases h

/-- 下限 `δ` が `pre` で始まらないとき：`δ < pre` -/
theorem lt_pre_of_tail_none {X δ R : Tm} {pre : List Tm} (hX : WNF X)
    (hsX : summands X = pre ++ [R]) (hδ : WNF δ) (hδX : Lt δ X) (h : tailRaw (some δ) pre = none) :
    Lt δ (ofSummands pre) := by
  have hXn : NFL (pre ++ [R]) := by rw [← hsX]; exact nfl_summands hX
  have hpre := nfl_append_left hXn
  have hnp : ¬ (pre.length ≤ (summands δ).length ∧ (summands δ).take pre.length = pre) := by
    intro hc
    simp only [tailRaw] at h
    rw [ite_eq_left hc] at h
    cases h
  rcases lt_split hX hsX hδ hδX with hle | ⟨y', -, -, -, hs, -⟩
  · rcases hle with e | hlt
    · exfalso
      apply hnp
      have : summands δ = pre := by rw [e, summands_ofSummands pre (nfl_principal hpre)]
      rw [this]
      exact ⟨Nat.le_refl _, List.take_length⟩
    · exact hlt
  · exfalso
    apply hnp
    rw [hs]
    exact ⟨by simp, by simp⟩

/-- 素の近似（対角化の調整なし）の `mkApp` と、調整 `c` の性質 -/
theorem mkApp_plain {π X R : Tm} {pre : List Tm} {r : SeqD} (ht : WNF (.Psi π X))
    (hsX : summands X = pre ++ [R]) (hns : ¬ isSucc X = true) (x0 : Tm) :
    ∃ c, mkApp π (.psi π) pre R r zero zero = some (.app π (.psi π) pre R r zero c) ∧
      AdjOK π pre R x0 c := by
  have hP := ht.psi
  have hX := hP.aF
  have hπ := hP.piF
  have hXn : NFL (pre ++ [R]) := by rw [← hsX]; exact nfl_summands hX
  have hpre : NFL pre := nfl_append_left hXn
  have hPF := wnf_ofSummands hpre
  have hR := hXn.1 R (by simp)
  have hR0 : R ≠ .zero := by intro e; rw [e] at hR; cases hR.2
  have hRns : ¬ isSucc R = true := by rw [← isSucc_of_last hsX hR.2]; exact hns
  have hX0 : X ≠ .zero := by intro e; rw [e] at hsX; simp [summands] at hsX
  have adj0 : (∀ x, WNF x → Le x0 x →
      validR π (oadd (ofSummands pre) (oadd .zero x)) = true) → AdjOK π pre R x0 .zero :=
    fun hv => ⟨WNF.zero, zero_lt hR0, fun _ _ _ _ _ _ _ => inC_zero _ _, hv⟩
  unfold mkApp
  simp only [ne_eq, not_true_eq_false, false_and, ↓reduceIte, Gen.tgt?]
  split
  · -- `pre` は下限の先頭部分でない
    rename_i hrt
    refine ⟨.zero, rfl, adj0 (fun x hx _ => validR_iff.mpr (fun δ hδ => ?_))⟩
    obtain ⟨m, rfl⟩ := argR_some hδ
    rw [hδ] at hrt
    have hδF := hπ.xi.2.1
    have h1 := lt_pre_of_tail_none hX hsX hδF (hP.act m δ rfl) hrt
    exact lt_of_lt_of_leY hδF hPF (wnf_oadd hPF (wnf_oadd WNF.zero hx)) h1
      (le_oadd_leftW hPF (wnf_oadd WNF.zero hx))
  · rename_i rt hrt
    cases hδ : argR? π with
    | none => rw [hδ] at hrt; simp [tailRaw] at hrt
    | some δ =>
      obtain ⟨m, rfl⟩ := argR_some hδ
      rw [hδ] at hrt
      have hδF := hπ.xi.2.1
      obtain ⟨hrtF, hsδ, hδe⟩ := tailRaw_some hδF hrt
      have e1 : (summands X).dropLast = pre := by rw [hsX, List.dropLast_concat]
      have e2 : (summands X).getLast?.getD zero = R := by rw [hsX]; simp
      have hlt : Lt rt R := by
        have := lt_tailRaw hX hX0 hP (by rw [e1, hδ]; exact hrt)
        rw [e2] at this
        exact this
      have hleB : leB R rt = false := by
        cases e : leB R rt with
        | false => rfl
        | true =>
          exact absurd hlt (not_lt_of_leY hR.1 hrtF (le_of_ne_gtY hR.1 hrtF (leB_iff.mp e)))
      simp only [hleB, Bool.false_eq_true, ↓reduceIte]
      -- `δ` の加数は `C(g, d)` に入る
      have hδsum : ∀ g d, inC δ g d = true → ∀ s, s ∈ summands rt → inC s g d = true :=
        fun g d hC s hs => inC_of_mem_summands hδF hC (by rw [hsδ]; exact List.mem_append_right _ hs)
      have hδC : ∀ g d, inC (.Xi m δ) g d = true → ¬ Lt (.Xi m δ) d → inC δ g d = true := by
        intro g d hC hlt
        rcases inC_xi_iff.mp hC with h | ⟨h, -⟩
        · exact absurd h hlt
        · exact h
      -- `c = rt + 1`
      have hsF := succT_WNF hrtF
      refine ⟨sc rt, rfl, ⟨hsF, succT_lt_of_not_succ hrtF hR.1 hRns hlt,
        fun g d _ hg0 _ hπC hπd => inC_succT (inC_one hg0)
          ((inC_iff_summandsW hrtF).mpr (hδsum g d (hδC g d hπC hπd))),
        fun x hx _ => validR_iff.mpr (fun δ' hδ' => ?_)⟩⟩
      cases hδ'
      have h1 : Lt (oadd (ofSummands pre) rt) (oadd (ofSummands pre) (oadd (sc rt) x)) :=
        oadd_lt_oadd hPF hrtF (wnf_oadd hsF hx)
          (lt_of_lt_of_leY hrtF hsF (wnf_oadd hsF hx) (lt_succT rt) (le_oadd_leftW hsF hx))
      rw [← hδe] at h1
      exact h1

/-! ### 列の記述の形 -/

theorem cs_lim {π X : Tm} (hX : WNF X) (hX0 : X ≠ .zero) (hs : ¬ isSucc X = true) :
    cs π X = limitSeq π π (info X).sums := by
  have hd : (lastS (info X).sums).dom ≠ .one := fun h => hs ((lastS_dom_one_iff hX hX0).mp h)
  unfold cs cseq
  rw [ite_eq_right hX0]
  cases h : (lastS (info X).sums).dom with
  | one => exact absurd h hd
  | _ => rfl

theorem cs_lim_eq {π X R : Tm} {pre : List Tm} (hX : WNF X) (hsX : summands X = pre ++ [R])
    (hns : ¬ isSucc X = true) :
    cs π X = ((mkApp π (.psi π) pre R (info R).seq zero zero).map outFix).getD .none := by
  have hX0 : X ≠ .zero := by intro e; rw [e] at hsX; simp [summands] at hsX
  have e1 : preT (info X).sums = pre := by rw [preT_info, hsX, List.dropLast_concat]
  have e2 : lastT (info X).sums = R := by rw [lastT_info, hsX]; simp
  have e3 : lastS (info X).sums = (info R).seq := by rw [lastS_coh (coh_sums X), e2]
  rw [cs_lim hX hX0 hns]
  unfold limitSeq
  rw [e1, e2, e3]

/-- 塔の始点の置き換え（`outFix`）が働かない `app` -/
theorem outFix_app_eq {τ : Tm} {g : Gen} {pre : List Tm} {R : Tm} {r : SeqD} {P c : Tm}
    (h : ∀ σ, r.dom = .big σ → ltB σ τ = true ∨ outsideMode τ σ g pre R = false ∨
      ltB (Psi σ (oadd (ofSummands pre) R)) (Psi τ (oadd (ofSummands pre) R)) = false) :
    outFix (.app τ g pre R r P c) = .app τ g pre R r P c := by
  simp only [outFix]
  cases hd : r.dom with
  | big σ =>
    cases σ with
    | Xi m e =>
      dsimp only
      have hc : (!ltB (Xi m e) τ && outsideMode τ (Xi m e) g pre R &&
          ltB (Psi (Xi m e) (oadd (ofSummands pre) R)) (Psi τ (oadd (ofSummands pre) R))) = false := by
        rcases h _ hd with h' | h' | h' <;> simp [h']
      rw [ite_eq_right (by rw [hc]; decide)]
    | _ => rfl
  | _ => rfl

/-- 塔の始点の置き換えが働かない `mkApp` の結果 -/
theorem cs_lim_app {π X R : Tm} {pre : List Tm} {c : Tm} (hX : WNF X) (hsX : summands X = pre ++ [R])
    (hns : ¬ isSucc X = true)
    (hmk : mkApp π (.psi π) pre R (info R).seq zero zero = some (.app π (.psi π) pre R (info R).seq zero c))
    (h : ∀ σ, (info R).seq.dom = .big σ → ltB σ π = true ∨ outsideMode π σ (.psi π) pre R = false ∨
      ltB (Psi σ (oadd (ofSummands pre) R)) (Psi π (oadd (ofSummands pre) R)) = false) :
    cs π X = .app π (.psi π) pre R (info R).seq zero c := by
  rw [cs_lim_eq hX hsX hns, hmk, Option.map_some, Option.getD_some, outFix_app_eq h]

/-! ### 近似 `Ψ_π(pre ⊕ (c ⊕ x))` -/

/-- 近似の引数 `pre ⊕ (c ⊕ x)` -/
@[reducible] def apx (pre : List Tm) (c x : Tm) : Tm := oadd (ofSummands pre) (oadd c x)

section Approx

variable {π X R c x x0 : Tm} {pre : List Tm}

/-- 近似の引数 `A = pre ⊕ (c ⊕ x)` について：`A < X`、`X` の部分項・`π` の部分項で `Ψ_π(X)` 未満のものは
    `Ψ_π(A)` 未満、`X` の加数は `C(A, Ψ_π(A))` に入る -/
theorem approx_core (ht : WNF (.Psi π X)) (hsX : summands X = pre ++ [R]) (hcF : WNF c)
    (hcR : Lt c R) (hxF : WNF x) (hxR : Lt x R)
    (hgap : ∀ v, v ∈ subs R → v ≠ R → Lt v R → Lt v x)
    (hpos : x = .zero → ∀ v, v ∈ subs R → v = R) :
    WNF (apx pre c x) ∧ Lt (apx pre c x) X ∧
      (∀ v, v ∈ subs X → Lt v (.Psi π X) → Lt v (.Psi π (apx pre c x))) ∧
      (∀ v, v ∈ subs π → v ≠ π → Lt v π → Lt v (.Psi π (apx pre c x))) ∧
      (∀ s, s ∈ summands X → inC s (apx pre c x) (.Psi π (apx pre c x)) = true) := by
  have hP := ht.psi
  have hX := hP.aF
  have hπ := hP.piF
  have hT := hP.tgt
  have hXn : NFL (pre ++ [R]) := by rw [← hsX]; exact nfl_summands hX
  have hpre : NFL pre := nfl_append_left hXn
  have hPF := wnf_ofSummands hpre
  have hR := hXn.1 R (by simp)
  have hA'F : WNF (oadd c x) := wnf_oadd hcF hxF
  have hAF : WNF (apx pre c x) := wnf_oadd hPF hA'F
  have hA'R : Lt (oadd c x) R := oadd_lt_prin hcF hxF hR.2 hcR hxR
  have hAX : Lt (apx pre c x) X := by
    have := oadd_lt_oadd hPF hA'F hR.1 hA'R
    rw [← eq_oadd_of_summands hX hsX] at this
    exact this
  have hgap' : ∀ v, v ∈ subs R → v ≠ R → Lt v R → Lt v (oadd c x) := fun v hv hne hlt =>
    lt_of_lt_of_leY (hR.1.of_mem_subs hv) hxF hA'F (hgap v hv hne hlt) (le_oadd_right hcF hxF)
  have hpos' : oadd c x = .zero → ∀ v, v ∈ subs R → v = R :=
    fun h0 => hpos (oadd_eq_zero hcF hxF h0).2
  have hArg := argCond hX hsX hA'F hgap' hpos'
  have h3 : ∀ v, v ∈ subs X → Lt v (.Psi π X) → Lt v (.Psi π (apx pre c x)) := by
    intro v hv hvt
    have hvF := hX.of_mem_subs hv
    refine below_transfer hπ hT v hvF (fun Y hYs hYX => ?_) hvt
    obtain ⟨s, hs, hYs', hYne⟩ := psi_arg_in_summand (subs_trans hv hYs)
    exact hArg s hs Y hYs' hYne hYX
  refine ⟨hAF, hAX, h3, fun v hv hne hlt => sub_lt_psi hπ hT _ v hv hne (hπ.of_mem_subs hv) hlt,
    fun s hs => ?_⟩
  have hsC : inC s X (.Psi π X) = true := inC_of_mem_summands hX hP.Ca hs
  have hsX' : s ∈ subs X := mem_subs_of_mem_summands hs
  exact inC_mono_node s X _ _ _ hsC (fun v hv _ hvt => h3 v (subs_trans hsX' hv) hvt)
    (fun v hv hvs hvX => hArg s hs v hv (ne_of_size_lt hvs) hvX)

omit x0 c x R in
/-- 目標 `π` は `C(A, Ψ_π(A))` に入る（`π = Ξ_m(δ)` なら底の条件と `δ < A` から、`π = Ω_c` なら `c` の加数は
    `Ψ_π(A)` 未満） -/
theorem tgt_inC_approx (ht : WNF (.Psi π X)) {A : Tm} (hAF : WNF A) (hval : validR π A = true)
    (h4 : ∀ v, v ∈ subs π → v ≠ π → Lt v π → Lt v (.Psi π A)) :
    inC π A (.Psi π A) = true := by
  have hπ := ht.psi.piF
  have hT := ht.psi.tgt
  have hcut := cut_psi hπ hT hAF
  rcases hT with rfl | ⟨c, rfl, -⟩ | ⟨m, δ, rfl⟩
  · rw [inC_om]; exact inC_zero _ _
  · have hcF := hπ.om.1
    rw [inC_om, inC_iff_summandsW hcF]
    intro u hu
    have huF := (summands_WNF c hcF u hu).1
    have hus : u ∈ subs (Tm.Om c) := subs_om (mem_subs_of_mem_summands hu)
    have hlt : Lt u (.Om c) := lt_of_le_of_ltY huF hcF hπ (le_of_mem_summands hcF hu) (lt_om_selfY hπ)
    refine inC_of_lt_cut hcut A huF (h4 u hus (ne_of_size_lt ?_) hlt)
    have := size_le_of_mem_subs (mem_subs_of_mem_summands hu)
    simp only [Tm.size]; omega
  · have hδF := hπ.xi.2.1
    obtain ⟨-, hC⟩ := (baseOf_xi_iff m δ _).mp (base_selfY ht)
    have hδA : Lt δ A := validR_iff.mp hval δ rfl
    refine inC_xi_iff.mpr (Or.inr ⟨?_, hδA⟩)
    refine inC_mono_node δ δ _ _ _ hC (fun v hv _ hvt => ?_) (fun v hv _ hvδ => ?_)
    · have hvF := hδF.of_mem_subs hv
      refine h4 v (subs_xi hv) (ne_of_size_lt ?_) (lt_transY hvF ht hπ hvt (lt_psi_targetY ht))
      have := size_le_of_mem_subs hv
      simp only [Tm.size]; omega
    · exact lt_transY (hδF.of_mem_subs hv) hδF hAF hvδ hδA

/-- 調整 `c` は `C(A, Ψ_π(A))` に入る -/
theorem approx_cC (ht : WNF (.Psi π X)) (hadj : AdjOK π pre R x0 c) (hxF : WNF x)
    (hPF : WNF (ofSummands pre)) (hAF : WNF (apx pre c x)) (hval : validR π (apx pre c x) = true)
    (h4 : ∀ v, v ∈ subs π → v ≠ π → Lt v π → Lt v (.Psi π (apx pre c x))) :
    inC c (apx pre c x) (.Psi π (apx pre c x)) = true := by
  have hπ := ht.psi.piF
  have hT := ht.psi.tgt
  by_cases hc0 : c = .zero
  · rw [hc0]; exact inC_zero _ _
  · have hA0 : apx pre c x ≠ .zero := fun e =>
      hc0 (oadd_eq_zero hadj.cF hxF (oadd_eq_zero hPF (wnf_oadd hadj.cF hxF) e).2).1
    exact hadj.cC _ _ hAF hA0 (cut_psi hπ hT hAF) (tgt_inC_approx ht hAF hval h4)
      (fun h => Lt.irrefl _ (below_lt_tgt hπ hT π hπ h))

/-- 近似は標準形 -/
theorem approx_wnf (ht : WNF (.Psi π X)) (hsX : summands X = pre ++ [R]) (hcF : WNF c)
    (hxF : WNF x) (hAF : WNF (apx pre c x))
    (hsC : ∀ s, s ∈ summands X → inC s (apx pre c x) (.Psi π (apx pre c x)) = true)
    (hval : validR π (apx pre c x) = true)
    (hcC : inC c (apx pre c x) (.Psi π (apx pre c x)) = true)
    (hxC : inC x (apx pre c x) (.Psi π (apx pre c x)) = true) :
    WNF (.Psi π (apx pre c x)) := by
  have hP := ht.psi
  have hXn : NFL (pre ++ [R]) := by rw [← hsX]; exact nfl_summands hP.aF
  have hPF := wnf_ofSummands (nfl_append_left hXn)
  refine WNF.mk_psi ⟨hP.tgt, hP.piF, hAF, fun n p e => ?_, ?_⟩
  · subst e
    exact validR_iff.mp hval p rfl
  · refine inC_oadd hPF (wnf_oadd hcF hxF) ((inC_ofSummands pre).mpr (fun s hs => ?_))
      (inC_oadd hcF hxF hcC hxC)
    exact hsC s (by rw [hsX]; exact List.mem_append_left _ hs)

/-- 近似の上界：`Ψ_π(X) ∈ C(g, d)` なら `Ψ_π(A) ∈ C(g, d)` -/
theorem approx_ub (ht : WNF (.Psi π X)) (hsX : summands X = pre ++ [R])
    (hadj : AdjOK π pre R x0 c) (hxF : WNF x) (hyF : WNF (.Psi π (apx pre c x)))
    (hAX : Lt (apx pre c x) X) {g d : Tm} (hg : WNF g) (hg0 : g ≠ .zero) (hd : Cut d)
    (hC : inC (.Psi π X) g d = true) (hxub : inC R g d = true → inC x g d = true) :
    inC (.Psi π (apx pre c x)) g d = true := by
  have hP := ht.psi
  have hX := hP.aF
  have hπ := hP.piF
  have hXn : NFL (pre ++ [R]) := by rw [← hsX]; exact nfl_summands hX
  have hPF := wnf_ofSummands (nfl_append_left hXn)
  have hyt : Lt (.Psi π (apx pre c x)) (.Psi π X) := lt_psi_psi_same.mpr hAX
  by_cases hlt : Lt (.Psi π X) d
  · exact inC_of_lt_cut hd g hyF (hd _ _ hyF ht hyt hlt)
  · rcases inC_psi_iff.mp hC with h1 | ⟨hπC, hXC, hXg⟩
    · exact absurd h1 hlt
    · refine inC_psi_iff.mpr (Or.inr ⟨hπC, ?_, lt_transY hyF.psi.aF hX hg hAX hXg⟩)
      have hRC : inC R g d = true := inC_of_mem_summands hX hXC (by rw [hsX]; simp)
      refine inC_oadd hPF (wnf_oadd hadj.cF hxF) ((inC_ofSummands pre).mpr (fun s hs =>
        inC_of_mem_summands hX hXC (by rw [hsX]; exact List.mem_append_left _ hs)))
        (inC_oadd hadj.cF hxF ?_ (hxub hRC))
      exact hadj.cC g d hg hg0 hd hπC (fun h2 => hlt (hd _ _ ht hπ (lt_psi_targetY ht) h2))

omit x0 c x R in
/-- `pre ++ [R]` が加数の並びで `y < R` なら、`pre ⊕ y` の加数は `pre ++ summands y` -/
theorem summands_oadd_pre {R y : Tm} (hN : NFL (pre ++ [R])) (hy : WNF y) (hyR : Lt y R) :
    summands (oadd (ofSummands pre) y) = pre ++ summands y := by
  have hRF := (hN.1 R (by simp)).1
  have hn : NFL (pre ++ summands y) := by
    refine nfl_append (nfl_append_left hN) (nfl_summands hy) (fun a b ha hb => ?_)
    have haR : cmp R a ≠ .gt := nfl_append_ge hN a (List.mem_of_getLast? ha) R (by simp)
    have hbF := (summands_WNF _ hy b (List.mem_of_mem_head? hb)).1
    have hby : Le b y := le_of_mem_summands hy (List.mem_of_mem_head? hb)
    have hbR : Lt b R := lt_of_le_of_ltY hbF hy hRF hby hyR
    have haF := (hN.1 a (List.mem_append_left _ (List.mem_of_getLast? ha))).1
    exact ne_gt_of_le (Or.inr (lt_of_lt_of_leY hbF hRF haF hbR (le_of_ne_gtY hRF haF haR)))
  have h := summands_oadd_nfl hn
  rw [ofSummands_summands _ hy] at h
  exact h

omit x0 c x R in
/-- `pre ⊕ y ∈ C(g, d)`（`y < R`）なら `pre` の加数と `y` は `C(g, d)` に入る -/
theorem inC_oadd_pre {R y g d : Tm} (hN : NFL (pre ++ [R])) (hy : WNF y) (hyR : Lt y R)
    (h : inC (oadd (ofSummands pre) y) g d = true) :
    (∀ s, s ∈ pre → inC s g d = true) ∧ inC y g d = true := by
  have hA : WNF (oadd (ofSummands pre) y) := wnf_oadd (wnf_ofSummands (nfl_append_left hN)) hy
  have hs := summands_oadd_pre hN hy hyR
  refine ⟨fun s hs' => inC_of_mem_summands hA h (by rw [hs]; exact List.mem_append_left _ hs'), ?_⟩
  exact (inC_iff_summandsW hy).mpr (fun s hs' =>
    inC_of_mem_summands hA h (by rw [hs]; exact List.mem_append_right _ hs'))

/-- 近似の 2 点の上界：`Ψ_π(A_{x'}) ∈ C(g, d)` で、`x' ∈ C(g, d)` から `x ∈ C(g, d)` が出れば
    `Ψ_π(A_x) ∈ C(g, d)`（`x < x'`） -/
theorem approx_ub2 (ht : WNF (.Psi π X)) (hsX : summands X = pre ++ [R])
    (hadj : AdjOK π pre R x0 c) {x' : Tm} (hxF : WNF x) (hx'F : WNF x') (hx'R : Lt x' R)
    (hxx : Lt x x') (hyF : WNF (.Psi π (apx pre c x))) (hy'F : WNF (.Psi π (apx pre c x')))
    {g d : Tm} (hg : WNF g) (hg0 : g ≠ .zero) (hd : Cut d)
    (hC : inC (.Psi π (apx pre c x')) g d = true) (hxub : inC x' g d = true → inC x g d = true) :
    inC (.Psi π (apx pre c x)) g d = true := by
  have hP := ht.psi
  have hX := hP.aF
  have hπ := hP.piF
  have hXn : NFL (pre ++ [R]) := by rw [← hsX]; exact nfl_summands hX
  have hPF := wnf_ofSummands (nfl_append_left hXn)
  have hR := hXn.1 R (by simp)
  have hA'F : WNF (oadd c x') := wnf_oadd hadj.cF hx'F
  have hAA : Lt (apx pre c x) (apx pre c x') :=
    oadd_lt_oadd hPF (wnf_oadd hadj.cF hxF) hA'F (oadd_lt_oadd hadj.cF hxF hx'F hxx)
  have hyy : Lt (.Psi π (apx pre c x)) (.Psi π (apx pre c x')) := lt_psi_psi_same.mpr hAA
  by_cases hlt : Lt (.Psi π (apx pre c x')) d
  · exact inC_of_lt_cut hd g hyF (hd _ _ hyF hy'F hyy hlt)
  rcases inC_psi_iff.mp hC with h1 | ⟨hπC, hAC, hAg⟩
  · exact absurd h1 hlt
  have hcR : Lt (oadd c x') R := oadd_lt_prin hadj.cF hx'F hR.2 hadj.cR hx'R
  obtain ⟨hpre, hyC⟩ := inC_oadd_pre hXn hA'F hcR hAC
  have hπd : ¬ Lt π d := fun h2 => hlt (hd _ _ hy'F hπ (lt_psi_targetY hy'F) h2)
  have hcC := hadj.cC g d hg hg0 hd hπC hπd
  have hx'C := inC_of_oadd_right hadj.cF hx'F hyC
  refine inC_psi_iff.mpr (Or.inr ⟨hπC, ?_, lt_transY hyF.psi.aF hy'F.psi.aF hg hAA hAg⟩)
  exact inC_oadd hPF (wnf_oadd hadj.cF hxF) ((inC_ofSummands pre).mpr hpre)
    (inC_oadd hadj.cF hxF hcC (hxub hx'C))

/-- 近似の隙間：`Ψ_π(X)` の真の部分項で `Ψ_π(X)` 未満のものは `Ψ_π(A)` 未満 -/
theorem approx_gap (ht : WNF (.Psi π X)) {A : Tm}
    (h3 : ∀ v, v ∈ subs X → Lt v (.Psi π X) → Lt v (.Psi π A))
    (h4 : ∀ v, v ∈ subs π → v ≠ π → Lt v π → Lt v (.Psi π A)) :
    ∀ v, v ∈ subs (Tm.Psi π X) → v ≠ .Psi π X → Lt v (.Psi π X) → Lt v (.Psi π A) := by
  have hπ := ht.psi.piF
  intro v hv hne hvt
  simp only [subs, List.mem_cons, List.mem_append] at hv
  rcases hv with e | hvπ | hvX
  · exact absurd e hne
  · have hvπ' : Lt v π := lt_transY (hπ.of_mem_subs hvπ) ht hπ hvt (lt_psi_targetY ht)
    exact h4 v hvπ (Lt.ne hvπ') hvπ'
  · exact h3 v hvX hvt

end Approx


/-! ### `R` の列が `ω` 型 -/

/-- 極限 `X = pre + R` で `R` の列が `ω` 型のとき、`Ψ_π(X)[n] = Ψ_π(pre ⊕ (c ⊕ R[n]))` -/
theorem inv_psi_lim_nat {π X R : Tm} {pre : List Tm} (ht : WNF (.Psi π X))
    (hsX : summands X = pre ++ [R]) (hns : ¬ isSucc X = true)
    (hRd : dom R = .omega) (hRi : NatInv R) : Inv (.Psi π X) := by
  have hP := ht.psi
  have hX := hP.aF
  have hπ := hP.piF
  have hT := hP.tgt
  have hXn : NFL (pre ++ [R]) := by rw [← hsX]; exact nfl_summands hX
  have hPF := wnf_ofSummands (nfl_append_left hXn)
  have hRX : R ∈ summands X := by rw [hsX]; simp
  have hr : (info R).seq.dom = .omega := hRd
  have hfirst : (info R).seq.first = fundNat R 0 := by
    unfold SeqD.first; rw [hr]; rfl
  obtain ⟨c, hmk, hadj⟩ := mkApp_plain ht hsX hns ((info R).seq.first)
  rw [hfirst] at hadj
  have hcs : cs π X = .app π (.psi π) pre R (info R).seq zero c :=
    cs_lim_app hX hsX hns hmk (fun σ hd => by rw [hr] at hd; cases hd)
  have hdom : dom (.Psi π X) = .omega := by
    rw [dom_psi, hcs]
    simp only [SeqD.dom, hr]
  have hxF : ∀ n, WNF (fundNat R n) := hRi.props.nf
  have hf : ∀ n, fundNat (.Psi π X) n = .Psi π (apx pre c (fundNat R n)) := by
    intro n
    rw [fundNat_psi, hcs]
    simp only [SeqD.nat, hr]
    exact congrArg (Tm.Psi π) (combine_psi_zero pre hadj.cF (hxF n))
  have hmono0 : ∀ n, Le (fundNat R 0) (fundNat R n) := by
    intro n
    induction n with
    | zero => exact Or.inl rfl
    | succ n ih =>
      exact Or.inr (lt_of_le_of_ltY (hxF 0) (hxF n) (hxF (n + 1)) ih (hRi.props.mono n))
  have core := fun (n : Nat) => approx_core (π := π) ht hsX hadj.cF hadj.cR (hxF n)
    (hRi.props.lt n) (hRi.gap n) (fun h0 => absurd h0 (hRi.pos n))
  have hA'F : ∀ n, WNF (oadd c (fundNat R n)) := fun n => wnf_oadd hadj.cF (hxF n)
  have hA'0 : ∀ n, oadd c (fundNat R n) ≠ .zero := fun n e =>
    hRi.pos n (oadd_eq_zero hadj.cF (hxF n) e).2
  have hA0 : ∀ n, apx pre c (fundNat R n) ≠ .zero := fun n e =>
    hA'0 n (oadd_eq_zero hPF (hA'F n) e).2
  have hval : ∀ n, validR π (apx pre c (fundNat R n)) = true := fun n =>
    hadj.valid _ (hxF n) (hmono0 n)
  have hyF : ∀ n, WNF (.Psi π (apx pre c (fundNat R n))) := by
    intro n
    obtain ⟨hAF, -, -, h4, hsC⟩ := core n
    exact approx_wnf ht hsX hadj.cF (hxF n) hAF hsC (hval n)
      (approx_cC ht hadj (hxF n) hPF hAF (hval n) h4)
      (hRi.ub _ _ n hAF (hA0 n) (cut_psi hπ hT hAF) (hsC R hRX))
  have hAmono : ∀ n, Lt (apx pre c (fundNat R n)) (apx pre c (fundNat R (n + 1))) := fun n =>
    oadd_lt_oadd hPF (hA'F n) (hA'F (n + 1))
      (oadd_lt_oadd hadj.cF (hxF n) (hxF (n + 1)) (hRi.props.mono n))
  have hAle : ∀ i k, i ≤ k → Le (apx pre c (fundNat R i)) (apx pre c (fundNat R k)) := by
    intro i k hik
    induction hik with
    | refl => exact Or.inl rfl
    | step _ ih => exact Or.inr (lt_of_le_of_ltY (core i).1 (core _).1 (core _).1 ih (hAmono _))
  have hcof : ∀ Y, WNF Y → Lt Y X → ∃ n, Lt Y (apx pre c (fundNat R n)) := by
    intro Y hY hYX
    rcases lt_split hX hsX hY hYX with hle | ⟨y', hy', -, hy'R, -, hYe⟩
    · exact ⟨0, lt_of_le_of_ltY hY hPF (core 0).1 hle (lt_oadd_left hPF (hA'F 0) (hA'0 0))⟩
    · obtain ⟨n, hn⟩ := hRi.props.cof y' hy' hy'R
      refine ⟨n + 1, ?_⟩
      rw [hYe]
      refine oadd_lt_oadd hPF hy' (hA'F (n + 1)) ?_
      exact lt_of_lt_of_leY hy' (hxF (n + 1)) (hA'F (n + 1))
        (lt_of_le_of_ltY hy' (hxF n) (hxF (n + 1)) hn (hRi.props.mono n))
        (le_oadd_right hadj.cF (hxF (n + 1)))
  refine ⟨fun _ => ?_, fun σ hd => by rw [hdom] at hd; cases hd⟩
  refine ⟨⟨fun n => ?_, fun n => ?_, fun n => ?_, fun x hx hxt => ?_⟩, fun n => ?_,
    fun g d n hg hg0 hd hC => ?_, fun n v hv hne hvt => ?_, fun g d n hg hg0 hd hC => ?_⟩
  rotate_right
  · rw [hf] at hC ⊢
    exact approx_ub2 ht hsX hadj (hxF n) (hxF (n + 1)) (hRi.props.lt (n + 1)) (hRi.props.mono n)
      (hyF n) (hyF (n + 1)) hg hg0 hd hC (hRi.ub2 g d n hg hg0 hd)
  · rw [hf]; exact hyF n
  · rw [hf]; exact lt_psi_psi_same.mpr (core n).2.1
  · rw [hf, hf]; exact lt_psi_psi_same.mpr (hAmono n)
  · obtain ⟨n, hn⟩ := cof_psi_gen hπ hT (fun n => apx pre c (fundNat R n)) 0
      (fun i j => ⟨max i j,
        fun Y hY h => lt_of_lt_of_leY hY (core i).1 (core _).1 h (hAle i _ (Nat.le_max_left i j)),
        fun Y hY h => lt_of_lt_of_leY hY (core j).1 (core _).1 h (hAle j _ (Nat.le_max_right i j))⟩)
      hcof x hx hxt
    exact ⟨n, by rw [hf]; exact Or.inr hn⟩
  · rw [hf]; intro e; cases e
  · rw [hf]
    exact approx_ub ht hsX hadj (hxF n) (hyF n) (core n).2.1 hg hg0 hd hC
      (fun hRC => hRi.ub g d n hg hg0 hd hRC)
  · rw [hf]
    exact approx_gap ht (core n).2.2.1 (core n).2.2.2.1 v hv hne hvt

/-! ### `R` の列の共終数 `σ` が `π` 未満 -/

/-- 極限 `X = pre + R` で `R` の共終数 `σ` が `π` 未満のとき、`Ψ_π(X)[ξ] = Ψ_π(pre ⊕ (c ⊕ R[ξ]))` -/
theorem inv_psi_lim_big {π X R σ : Tm} {pre : List Tm} (ht : WNF (.Psi π X))
    (hsX : summands X = pre ++ [R]) (hns : ¬ isSucc X = true)
    (hRd : dom R = .big σ) (hRi : BigInv R σ) (hσπ : Lt σ π) : Inv (.Psi π X) := by
  have hP := ht.psi
  have hX := hP.aF
  have hπ := hP.piF
  have hT := hP.tgt
  have hXn : NFL (pre ++ [R]) := by rw [← hsX]; exact nfl_summands hX
  have hPF := wnf_ofSummands (nfl_append_left hXn)
  have hR := hXn.1 R (by simp)
  have hRX : R ∈ summands X := by rw [hsX]; simp
  have hRP := hRi.props
  have hσF := hRP.σF
  have hσ0 := hRP.pos
  have hσns := not_isSucc_reg hRi.σreg
  have hr : (info R).seq.dom = .big σ := hRd
  have hfirst : (info R).seq.first = fundBig R .zero := by
    unfold SeqD.first; rw [hr]; rfl
  obtain ⟨c, hmk, hadj⟩ := mkApp_plain ht hsX hns ((info R).seq.first)
  rw [hfirst] at hadj
  have hcs : cs π X = .app π (.psi π) pre R (info R).seq zero c :=
    cs_lim_app hX hsX hns hmk (fun σ' hd => by rw [hr] at hd; cases hd; exact Or.inl (ltB_iff.mpr hσπ))
  have hdom : dom (.Psi π X) = .big σ := by
    rw [dom_psi, hcs]
    simp only [SeqD.dom, hr, ltB_iff.mpr hσπ, ↓reduceIte]
  have hxF : ∀ ξ, WNF ξ → Lt ξ σ → WNF (fundBig R ξ) := hRP.nf
  have hf : ∀ ξ, WNF ξ → Lt ξ σ →
      fundBig (.Psi π X) ξ = .Psi π (apx pre c (fundBig R ξ)) := by
    intro ξ hξ hξσ
    rw [fundBig_psi, hcs]
    exact congrArg (Tm.Psi π) (combine_psi_zero pre hadj.cF (hxF ξ hξ hξσ))
  have hmono0 : ∀ ξ, WNF ξ → Lt ξ σ → Le (fundBig R .zero) (fundBig R ξ) := by
    intro ξ hξ hξσ
    by_cases h0 : ξ = .zero
    · rw [h0]; exact Or.inl rfl
    · exact Or.inr (hRP.mono .zero ξ WNF.zero hξ (zero_lt h0) hξσ)
  have core := fun (ξ : Tm) (hξ : WNF ξ) (hξσ : Lt ξ σ) =>
    approx_core (π := π) ht hsX hadj.cF hadj.cR (hxF ξ hξ hξσ) (hRP.lt ξ hξ hξσ)
      (fun v hv hne hlt => hRi.gapP hR.2 ξ v hξ hξσ hv hne hlt) (hRi.pos ξ hξ hξσ)
  have hA'F : ∀ ξ, WNF ξ → Lt ξ σ → WNF (oadd c (fundBig R ξ)) := fun ξ hξ hξσ =>
    wnf_oadd hadj.cF (hxF ξ hξ hξσ)
  have hval : ∀ ξ, WNF ξ → Lt ξ σ → validR π (apx pre c (fundBig R ξ)) = true :=
    fun ξ hξ hξσ => hadj.valid _ (hxF ξ hξ hξσ) (hmono0 ξ hξ hξσ)
  -- `σ < Ψ_π(X)`、`σ < Ψ_π(A)`
  have hRC : inC R X (.Psi π X) = true := inC_of_mem_summands hX hP.Ca hRX
  have hσt : Lt σ (.Psi π X) := coll_psiY ht hσF (hRi.σC X _ (Cut.of_wnf ht) hRC) hσπ
  have hσX : σ ∈ subs X := subs_trans (mem_subs_of_mem_summands hRX) hRi.σsub
  have hσy : ∀ ξ, WNF ξ → Lt ξ σ → Lt σ (.Psi π (apx pre c (fundBig R ξ))) :=
    fun ξ hξ hξσ => (core ξ hξ hξσ).2.2.1 σ hσX hσt
  have hyF : ∀ ξ, WNF ξ → Lt ξ σ → WNF (.Psi π (apx pre c (fundBig R ξ))) := by
    intro ξ hξ hξσ
    obtain ⟨hAF, -, -, h4, hsC⟩ := core ξ hξ hξσ
    have hcut := cut_psi hπ hT hAF
    refine approx_wnf ht hsX hadj.cF (hxF ξ hξ hξσ) hAF hsC (hval ξ hξ hξσ)
      (approx_cC ht hadj (hxF ξ hξ hξσ) hPF hAF (hval ξ hξ hξσ) h4) ?_
    by_cases hA0 : apx pre c (fundBig R ξ) = .zero
    · have hx0 := (oadd_eq_zero hadj.cF (hxF ξ hξ hξσ)
        (oadd_eq_zero hPF (hA'F ξ hξ hξσ) hA0).2).2
      rw [hx0]; exact inC_zero _ _
    · have hσy' := hσy ξ hξ hξσ
      have hbF := wnf_base hσF hRi.σreg
      exact hRi.ub _ _ ξ hAF hA0 hcut hξ hξσ
        (inC_of_lt_cut hcut _ hbF (hcut _ _ hbF hσF (base_lt hσF hRi.σreg) hσy'))
        (hsC R hRX)
        (inC_of_lt_cut hcut _ hξ (hcut _ _ hξ hσF hξσ hσy'))
  have hAlt : ∀ ξ η, WNF ξ → WNF η → Lt ξ η → Lt η σ →
      Lt (apx pre c (fundBig R ξ)) (apx pre c (fundBig R η)) := by
    intro ξ η hξ hη hξη hησ
    have hξσ := lt_transY hξ hη hσF hξη hησ
    exact oadd_lt_oadd hPF (hA'F ξ hξ hξσ) (hA'F η hη hησ)
      (oadd_lt_oadd hadj.cF (hxF ξ hξ hξσ) (hxF η hη hησ) (hRP.mono ξ η hξ hη hξη hησ))
  -- 閉じた点での共終性
  have hcloS : ∀ β, WNF β → Lt .zero β → Lt β σ → ∀ x, WNF x → Lt x (.Psi π X) →
      (∀ f, f ∈ lfr σ x → Lt f β) → Lt x (.Psi π (apx pre c (fundBig R β))) := by
    intro β hβ hβ0 hβσ x
    induction x using size_induction with
    | h x ih =>
    intro hx hxt hfr
    have hyβ := hyF β hβ hβσ
    by_cases hxσ : Lt x σ
    · have h1 := hfr x (by rw [lfr_of_lt hxσ]; exact List.mem_singleton.mpr rfl)
      exact lt_transY hx hβ hyβ h1 (lt_transY hβ hσF hyβ hβσ (hσy β hβ hβσ))
    · refine psi_step ht hyβ hx hxt (fun w hw => ?_) (fun ρ a e hρt => ?_) (fun a e => ?_)
      · have hwx := parF_lt hx hw
        have hwF := hx.of_mem_subs (parF_mem_subs hw)
        refine ih w (parL_sub (parF_sub_parL hw)).2 hwF (lt_transY hwF hx ht hwx hxt) (fun f hf => ?_)
        obtain ⟨g, hg, hfg⟩ := lfr_of_parF hσF hx hxσ hw hf
        exact lt_of_le_of_ltY (hwF.of_mem_subs (lfr_spec hf).1) (hx.of_mem_subs (lfr_spec hg).1)
          hβ hfg (hfr g hg)
      · subst e
        exact ih ρ (by simp only [Tm.size]; omega) hx.psi.piF hρt
          (fun f hf => hfr f ((mem_lfr_psi hxσ).mpr (Or.inl hf)))
      · subst e
        have haF := hx.psi.aF
        have haX : Lt a X := lt_psi_psi_same.mp hxt
        have hxβF := hxF β hβ hβσ
        rcases lt_split hX hsX haF haX with hle | ⟨a', ha', ha'0, ha'R, hsa, hae⟩
        · have hxβ0 : fundBig R β ≠ .zero := by
            intro e
            have h1 := hRi.ge β hβ hβσ
            rw [e] at h1
            rcases h1 with e' | h1
            · exact absurd hβ0 (by rw [e']; exact Lt.irrefl _)
            · exact not_lt_zero _ h1
          have hA0 : oadd c (fundBig R β) ≠ .zero := fun e =>
            hxβ0 (oadd_eq_zero hadj.cF hxβF e).2
          exact lt_of_le_of_ltY haF hPF (core β hβ hβσ).1 hle
            (lt_oadd_left hPF (hA'F β hβ hβσ) hA0)
        · rw [hae]
          have hfa : ∀ f, f ∈ lfr σ a' → Lt f β := fun f hf => by
            obtain ⟨g, hg, hfg⟩ := lfr_suffix hσF pre haF ha' ha'0 hsa hf
            exact lt_of_le_of_ltY (ha'.of_mem_subs (lfr_spec hf).1) (haF.of_mem_subs (lfr_spec hg).1)
              hβ hfg (hfr g ((mem_lfr_psi hxσ).mpr (Or.inr hg)))
          have h1 := hRi.lclo a' β ha' ha'R hβ hβ0 hβσ hfa
          exact oadd_lt_oadd hPF ha' (hA'F β hβ hβσ)
            (lt_of_lt_of_leY ha' hxβF (hA'F β hβ hβσ) h1 (le_oadd_right hadj.cF hxβF))
  refine ⟨(fun hd => by rw [hdom] at hd; cases hd), fun σ' hd => ?_⟩
  rw [hdom] at hd
  cases hd
  refine {
    props := ⟨hσF, hσ0, fun ξ hξ hξσ => ?_, fun ξ hξ hξσ => ?_,
      fun ξ η hξ hη hξη hησ => ?_, fun x hx hxt => ?_⟩
    σreg := hRi.σreg
    σsub := subs_psi_a hσX
    σle := Or.inr hσt
    pos := fun ξ hξ hξσ h0 => ?_
    σC := fun g d hd hC => ?_
    ub := fun g d ξ hg hg0 hd hξ hξσ hbC hC hξC => ?_
    lo := fun g d ξ hd hξ hξσ hC => ?_
    ge := fun ξ hξ hξσ => ?_
    gap := fun ξ v hξ hξσ hv hne hvt => ?_
    gapP := fun _ ξ v hξ hξσ hv hne hvt => ?_
    lclo := fun x β hx hxt hβ hβ0 hβσ hfr => by
      rw [hf β hβ hβσ]; exact hcloS β hβ hβ0 hβσ x hx hxt hfr
    nsucc := fun ξ hξ hξσ _ _ => by
      rw [hf ξ hξ hξσ]
      intro he
      have hπ0 : π = .Om .zero := by simp [isSucc, summands, one] at he; exact he.1
      subst hπ0
      exact not_lt_om_zero_of_reg hσF hRi.σreg hσπ
    bge := fun ξ hξ hξσ => by
      rw [hf ξ hξ hξσ]
      have hbF := wnf_base hσF hRi.σreg
      exact Or.inr (lt_transY hbF hσF (hyF ξ hξ hξσ) (base_lt hσF hRi.σreg) (hσy ξ hξ hξσ))
    lbK := fun m e _ ξ hξ hξσ => by
      rw [hf ξ hξ hξσ, ← e]
      exact Or.inr (hσy ξ hξ hξσ)
    lbS := fun m e hlt ξ hξ hξσ => by
      rw [hf ξ hξ hξσ]
      have hm : 1 ≤ m := by have h := hσF; rw [e] at h; exact h.M
      refine Or.inr (below_transfer hπ hT (succM m) (WNF.succM hm) (fun Y hY _ => ?_) hlt)
      have hπ0 := psi_mem_subs_succM hY
      subst hπ0
      exact absurd hσπ (not_lt_om_zero_of_reg hσF hRi.σreg)
    ub2 := fun g d ξ η hg hg0 hd hξ hη hξη hησ hbC hξC hC => by
      have hξσ := lt_transY hξ hη hσF hξη hησ
      rw [hf η hη hησ] at hC
      rw [hf ξ hξ hξσ]
      exact approx_ub2 ht hsX hadj (hxF ξ hξ hξσ) (hxF η hη hησ) (hRP.lt η hη hησ)
        (hRP.mono ξ η hξ hη hξη hησ) (hyF ξ hξ hξσ) (hyF η hη hησ) hg hg0 hd hC
        (hRi.ub2 g d ξ η hg hg0 hd hξ hη hξη hησ hbC hξC)
    bw := fun g d ξ L hd hξ hξσ hL hσL hC => by
      rw [hf ξ hξ hξσ] at hC
      have hbF := wnf_base hσF hRi.σreg
      have hbσ := base_lt hσF hRi.σreg
      rcases inC_psi_iff.mp hC with h1 | ⟨-, hAC, -⟩
      · refine ⟨base σ, hbF, inC_of_lt_cut hd g hbF (hd _ _ hbF (hyF ξ hξ hξσ)
          (lt_transY hbF hσF (hyF ξ hξ hξσ) hbσ (hσy ξ hξ hξσ)) h1), Or.inl rfl,
          lt_transY hbF hσF hL hbσ hσL⟩
      · exact hRi.bw g d ξ L hd hξ hξσ hL hσL
          (inC_of_oadd_right hadj.cF (hxF ξ hξ hξσ) (inC_of_oadd_right hPF (hA'F ξ hξ hξσ) hAC)) }
  · rw [hf ξ hξ hξσ]; exact hyF ξ hξ hξσ
  · rw [hf ξ hξ hξσ]; exact lt_psi_psi_same.mpr (core ξ hξ hξσ).2.1
  · rw [hf ξ hξ (lt_transY hξ hη hσF hξη hησ), hf η hη hησ]
    exact lt_psi_psi_same.mpr (hAlt ξ η hξ hη hξη hησ)
  · -- 共終性
    have hone : Lt one σ := one_lt_reg hσF hRi.σreg hσ0
    have hcof : ∀ Y, WNF Y → Lt Y X →
        ∃ i : {ξ : Tm // WNF ξ ∧ Lt ξ σ}, Lt Y (apx pre c (fundBig R i.1)) := by
      intro Y hY hYX
      rcases lt_split hX hsX hY hYX with hle | ⟨y', hy', -, hy'R, -, hYe⟩
      · refine ⟨⟨one, WNF.one, hone⟩, ?_⟩
        have hx1 : fundBig R one ≠ .zero := fun e => by
          have := hRP.mono .zero one WNF.zero WNF.one (zero_lt (by intro e'; cases e')) hone
          rw [e] at this
          exact not_lt_zero _ this
        have hA1 : oadd c (fundBig R one) ≠ .zero := fun e =>
          hx1 (oadd_eq_zero hadj.cF (hxF one WNF.one hone) e).2
        exact lt_of_le_of_ltY hY hPF (core one WNF.one hone).1 hle
          (lt_oadd_left hPF (hA'F one WNF.one hone) hA1)
      · obtain ⟨ξ, hξ, hξσ, hle⟩ := hRP.cof y' hy' hy'R
        have hsξ := succT_WNF hξ
        have hsσ : Lt (succT ξ) σ := succT_lt_of_not_succ hξ hσF hσns hξσ
        refine ⟨⟨succT ξ, hsξ, hsσ⟩, ?_⟩
        rw [hYe]
        refine oadd_lt_oadd hPF hy' (hA'F _ hsξ hsσ) ?_
        exact lt_of_lt_of_leY hy' (hxF _ hsξ hsσ) (hA'F _ hsξ hsσ)
          (lt_of_le_of_ltY hy' (hxF ξ hξ hξσ) (hxF _ hsξ hsσ) hle
            (hRP.mono ξ (succT ξ) hξ hsξ (lt_succT ξ) hsσ))
          (le_oadd_right hadj.cF (hxF _ hsξ hsσ))
    have hdir : ∀ i j : {ξ : Tm // WNF ξ ∧ Lt ξ σ}, ∃ k : {ξ : Tm // WNF ξ ∧ Lt ξ σ},
        (∀ Y, WNF Y → Lt Y (apx pre c (fundBig R i.1)) → Lt Y (apx pre c (fundBig R k.1))) ∧
        (∀ Y, WNF Y → Lt Y (apx pre c (fundBig R j.1)) → Lt Y (apx pre c (fundBig R k.1))) := by
      intro i j
      have hAi := (core i.1 i.2.1 i.2.2).1
      have hAj := (core j.1 j.2.1 j.2.2).1
      rcases triY i.2.1 j.2.1 with h | h | h
      · exact ⟨j, fun Y hY hlt => lt_transY hY hAi hAj hlt (hAlt i.1 j.1 i.2.1 j.2.1 h j.2.2),
          fun Y _ hlt => hlt⟩
      · refine ⟨j, fun Y _ hlt => ?_, fun Y _ hlt => hlt⟩
        rw [← h]; exact hlt
      · exact ⟨i, fun Y _ hlt => hlt,
          fun Y hY hlt => lt_transY hY hAj hAi hlt (hAlt j.1 i.1 j.2.1 i.2.1 h i.2.2)⟩
    obtain ⟨i, hi⟩ := cof_psi_gen hπ hT
      (fun i : {ξ : Tm // WNF ξ ∧ Lt ξ σ} => apx pre c (fundBig R i.1))
      ⟨.zero, WNF.zero, hσ0⟩ hdir hcof x hx hxt
    exact ⟨i.1, i.2.1, i.2.2, by rw [hf i.1 i.2.1 i.2.2]; exact Or.inr hi⟩
  · rw [hf ξ hξ hξσ] at h0; cases h0
  · by_cases hlt : Lt (.Psi π X) d
    · exact inC_of_lt_cut hd g hσF (hd _ _ hσF ht hσt hlt)
    · rcases inC_psi_iff.mp hC with h1 | ⟨-, hXC, -⟩
      · exact absurd h1 hlt
      · exact hRi.σC g d hd (inC_of_mem_summands hX hXC hRX)
  · rw [hf ξ hξ hξσ]
    exact approx_ub ht hsX hadj (hxF ξ hξ hξσ) (hyF ξ hξ hξσ) (core ξ hξ hξσ).2.1 hg hg0 hd hC
      (fun hRC' => hRi.ub g d ξ hg hg0 hd hξ hξσ hbC hRC' hξC)
  · rw [hf ξ hξ hξσ] at hC
    rcases inC_psi_iff.mp hC with h1 | ⟨-, hAC, -⟩
    · have hξy : Lt ξ (.Psi π (apx pre c (fundBig R ξ))) :=
        cut_psi hπ hT (core ξ hξ hξσ).1 ξ σ hξ hσF hξσ (hσy ξ hξ hξσ)
      exact inC_of_lt_cut hd g hξ (hd _ _ hξ (hyF ξ hξ hξσ) hξy h1)
    · exact hRi.lo g d ξ hd hξ hξσ
        (inC_of_oadd_right hadj.cF (hxF ξ hξ hξσ) (inC_of_oadd_right hPF (hA'F ξ hξ hξσ) hAC))
  · rw [hf ξ hξ hξσ]
    exact Or.inr (cut_psi hπ hT (core ξ hξ hξσ).1 ξ σ hξ hσF hξσ (hσy ξ hξ hξσ))
  · rw [hf ξ hξ hξσ]
    exact Or.inr (approx_gap ht (core ξ hξ hξσ).2.2.1 (core ξ hξ hξσ).2.2.2.1 v hv hne hvt)
  · rw [hf ξ hξ hξσ]
    exact approx_gap ht (core ξ hξ hξσ).2.2.1 (core ξ hξ hξσ).2.2.2.1 v hv hne hvt

/-! ### 残りの場合 -/

/-- 対角化の場合：極限 `X = pre + R` で、`R` の共終数 `σ` が `π` 以上 -/
def PsiDiagInv : Prop :=
  ∀ π X R σ pre, WNF (.Psi π X) → summands X = pre ++ [R] → ¬ isSucc X = true →
    dom R = .big σ → BigInv R σ → ¬ Lt σ π →
    (∀ u, u.size < (Tm.Psi π X).size → WNF u → Inv u) → Inv (.Psi π X)

/-- `Ξ_n(p)` への崩壊で `X` が後者の場合 -/
def PsiXiSuccInv : Prop :=
  ∀ n p X, WNF (.Psi (.Xi n p) X) → isSucc X = true →
    (∀ u, u.size < (Tm.Psi (.Xi n p) X).size → WNF u → Inv u) → Inv (.Psi (.Xi n p) X)

theorem psiRestInv_of (hD : PsiDiagInv) (hS : PsiXiSuccInv) : PsiRestInv := by
  intro π X ht hX0 hsx ih
  by_cases hs : isSucc X = true
  · obtain ⟨n, p, rfl⟩ := hsx hs
    exact hS n p X ht hs ih
  · have hX := ht.psi.aF
    have hne := summands_ne_nil hX0
    obtain ⟨pre, R, hsX⟩ : ∃ pre R, summands X = pre ++ [R] :=
      ⟨_, _, (List.dropLast_concat_getLast hne).symm⟩
    have hRX : R ∈ summands X := by rw [hsX]; simp
    have hR := summands_WNF X hX R hRX
    have hRsz : R.size < (Tm.Psi π X).size := by
      have := size_le_of_mem_subs (mem_subs_of_mem_summands hRX)
      simp only [Tm.size]; omega
    have hRi := ih R hRsz hR.1
    cases hd : dom R with
    | zero =>
      have := (dom_eq_zero_iff hR.1).mp hd
      rw [this] at hR
      cases hR.2
    | one =>
      exact absurd (by rw [isSucc_of_last hsX hR.2]; exact (dom_eq_one_iff hR.1).mp hd) hs
    | omega => exact inv_psi_lim_nat ht hsX hs hd (hRi.1 hd)
    | big σ =>
      have hB := hRi.2 σ hd
      by_cases hσπ : Lt σ π
      · exact inv_psi_lim_big ht hsX hs hd hB hσπ
      · exact hD π X R σ pre ht hsX hs hd hB hσπ ih

end MahloOCF.FS
