import Mahlo.FS.KTop

/-! `M_m` への対角化（`R` の共終数が `M_m`）のうち、近似が `M_m⁺` 未満の場合（`canonK`）。

近似 `t[n] = Ψ_π(pre ⊕ (c ⊕ R[γ_n]))`、添字は正準な塔 `γ_0 = kTop`（目標の前線の、塔の障害の最大のもの。
`0` からの塔の 1 段目がそれを越えるなら `0`）、`γ_{k+1} = Ξ_m(pre ⊕ R[γ_k])`。調整 `c` は `R[γ_0]` で有効にする。

* 塔の項は標準形で、`γ_k` は `Ξ_m(B_k)` の成分なので `γ_k < γ_{k+1}`（`coll_xi0`）。
* 目標の前線の元は障害が塔の 1 段目未満なので塔の下にあり（`kTop_hull`）、目標そのものも塔の下にある。
  したがって `t` は塔の下にあり、`C(X, t)` の `M_m` 未満の元は全て塔の下にある。 -/

namespace MahloOCF.FS

open Tm

/-! ### 目標の前線 -/

/-- 目標 `π`（`π ≥ d`）が `C(g, d)` に入れば、`π` の前線の元も入る -/
theorem fr_inC_of_tgt {π g d : Tm} (hπ : WNF π) (hT : IsTgt π) (hg : WNF g) (hd : Cut d)
    (hC : inC π g d = true) (hπd : ¬ Lt π d) : ∀ e, e ∈ fr π π → inC e g d = true := by
  have hsub : ∀ x, WNF x → ∀ w, w ∈ subs x → ¬ Lt w π → ¬ Lt w d := fun x hx w hw hwπ hwd =>
    hπd (hd.le hπ (hx.of_mem_subs hw) (le_of_not_ltY (hx.of_mem_subs hw) hπ hwπ) hwd)
  intro e he
  rcases hT with rfl | ⟨c, rfl, -⟩ | ⟨m, δ, rfl⟩
  · simp [fr] at he
  · have hcF := hπ.om.1
    rw [fr_self_om] at he
    rw [inC_om] at hC
    have h0 : inC c g (.Om c) = true := inC_of_lt_cut (Cut.of_wnf hπ) g hcF (lt_om_selfY hπ)
    exact (inC_fr c h0 (hsub c hcF) (fun _ _ h => h)).mp hC e he
  · have hδF := hπ.xi.2.1
    rw [fr_self_xi] at he
    rcases inC_xi_iff.mp hC with h | ⟨hδC, hδg⟩
    · exact absurd h hπd
    · exact (inC_fr δ (xi_selfY hπ) (hsub δ hδF)
        (fun v hv hvδ => lt_transY (hδF.of_mem_subs hv) hδF hg hvδ hδg)).mp hδC e he

/-! ### 列の記述の評価（`canonK`） -/

theorem gam_K_zero {π : Tm} {m : Nat} {pre : List Tm} {R : Tm} {r : SeqD} {c P : Tm}
    (hcan : canonK (.M m) (.psi π) pre R = true) :
    gam π (.M m) (.psi π) pre R r c P 0 = kTop π m pre R r := by
  simp only [gam, hcan, ↓reduceIte]

theorem gam_K_succ {π : Tm} {m : Nat} {pre : List Tm} {R : Tm} {r : SeqD} {c P : Tm}
    (hcan : canonK (.M m) (.psi π) pre R = true) (k : Nat) :
    gam π (.M m) (.psi π) pre R r c P (k + 1) =
      col (.M m) (oadd (ofSummands pre) (r.big (gam π (.M m) (.psi π) pre R r c P k))) k := by
  simp only [gam, hcan, ↓reduceIte]

theorem col_M_le {m k : Nat} {δ : Tm} (h : leB δ (succM m) = true) : col (.M m) δ k = .Xi m δ := by
  simp only [col, h, ↓reduceIte]

theorem nat_app_K {π : Tm} {m : Nat} {pre : List Tm} {R : Tm} {r : SeqD} {c : Tm}
    (hd : r.dom = .big (.M m)) (hlt : ltB (.M m) π = false) (hcan : canonK (.M m) (.psi π) pre R = true)
    (n : Nat) :
    (SeqD.app π (.psi π) pre R r .zero c).nat n =
      .Psi π (combine (.psi π) pre c .zero (r.big (gam π (.M m) (.psi π) pre R r c .zero n))) := by
  simp only [SeqD.nat, hd, hlt, Bool.false_eq_true, ↓reduceIte, argOf, hcan, Gen.ap]

/-! ### 補題 -/

/-- `a ≤ b` でない（`leB a b = false`）なら `b < a` -/
theorem lt_of_leB_false {a b : Tm} (ha : WNF a) (hb : WNF b) (h : leB a b = false) : Lt b a := by
  refine lt_of_gtY ha hb ?_
  unfold leB at h
  cases e : cmp a b with
  | lt => rw [e] at h; exact absurd h (by decide)
  | eq => rw [e] at h; exact absurd h (by decide)
  | gt => rfl

theorem inC_kTerm (n : Nat) (g d : Tm) : inC (kTerm n) g d = true := by
  unfold kTerm; split
  · exact inC_zero _ _
  · exact inC_M _ _ _

/-- `X = pre + R` の加数は段 `pre ⊕ A'`（`A'` は `R` の隙間を満たす）に移せる -/
theorem summand_inC_transfer {X R A' D : Tm} {pre : List Tm} (hX : WNF X)
    (hsX : summands X = pre ++ [R]) (hA : WNF A') (hgap : ∀ v, v ∈ subs R → v ≠ R → Lt v R → Lt v A')
    (hpos : A' = .zero → ∀ v, v ∈ subs R → v = R) (hXC : inC X X D = true) :
    ∀ s, s ∈ summands X → inC s (oadd (ofSummands pre) A') D = true := by
  have hArg := argCond hX hsX hA hgap hpos
  intro s hs
  exact inC_mono_node s X D _ D (inC_of_mem_summands hX hXC hs) (fun _ _ _ h => h)
    (fun v hv hvs hvX => hArg s hs v hv (ne_of_size_lt hvs) hvX)

/-- 目標 `π` は `C(Y, π)` に入る（`π = Ξ_m(δ)` なら `δ < Y`） -/
theorem tgt_inC_self {π Y : Tm} (hπ : WNF π) (hT : IsTgt π) (hY : WNF Y)
    (hv : ∀ δ, argR? π = some δ → Lt δ Y) : inC π Y π = true := by
  rcases hT with rfl | ⟨c, rfl, -⟩ | ⟨m, δ, rfl⟩
  · rw [inC_om]; exact inC_zero _ _
  · rw [inC_om]; exact inC_of_lt_cut (Cut.of_wnf hπ) Y hπ.om.1 (lt_om_selfY hπ)
  · have hδF := hπ.xi.2.1
    have hδY := hv δ rfl
    refine inC_xi_iff.mpr (Or.inr ⟨?_, hδY⟩)
    exact inC_mono δ δ _ Y _ (xi_selfY hπ) (fun _ _ h => h)
      (fun v hv' hvδ => lt_transY (hδF.of_mem_subs hv') hδF hY hvδ hδY)

/-! ### `canonK` の列の不変量 -/


theorem inv_psi_diag_K {π X R : Tm} {m : Nat} {pre : List Tm} (ht : WNF (.Psi π X))
    (hsX : summands X = pre ++ [R]) (hns : ¬ isSucc X = true)
    (hRd : dom R = .big (.M m)) (hRi : BigInv R (.M m)) (hMπ : ¬ Lt (.M m) π)
    (hold : kOld m pre R = false) : Inv (.Psi π X) := by
  have hP := ht.psi
  have hX := hP.aF
  have hπ := hP.piF
  have hπT := hP.tgt
  have hXn : NFL (pre ++ [R]) := by rw [← hsX]; exact nfl_summands hX
  have hPF := wnf_ofSummands (nfl_append_left hXn)
  have hR := hXn.1 R (by simp)
  have hRX : R ∈ summands X := by rw [hsX]; simp
  have hRP := hRi.props
  have hMF : WNF (.M m) := hRP.σF
  have hm : 1 ≤ m := hMF.M
  have hπM : Lt π (.M m) := by
    rcases triY hπ hMF with h | e | h
    · exact h
    · exact absurd e (hπT.notM m)
    · exact absurd h hMπ
  have htM : Lt (.Psi π X) (.M m) := lt_transY ht hπ hMF (lt_psi_targetY ht) hπM
  have hMR : Le (.M m) R := hRi.σle
  have hr : (info R).seq.dom = .big (.M m) := hRd
  have hlt : ltB (.M m) π = false := by
    cases e : ltB (.M m) π with
    | false => rfl
    | true => exact absurd (ltB_iff.mp e) hMπ
  have hcan : canonK (.M m) (.psi π) pre R = true := by
    show (!kOld m pre R) = true
    rw [hold]; rfl
  have hXe : X = oadd (ofSummands pre) R := eq_oadd_of_summands hX hsX
  have hXS : Lt X (succM m) := by
    have h1 : leB (succM m) X = false := by rw [hXe]; exact hold
    exact lt_of_leB_false (WNF.succM hm) hX h1
  -- 始点と調整 `c`
  obtain ⟨hG0F, hG0M, hG0C⟩ := kTop_spec (pre := pre) (R := R) (r := (info R).seq) hm hπ hπM
  obtain ⟨c, hmk, hadj⟩ := mkApp_plain ht hsX hns (fundBig R (kTop π m pre R (info R).seq))
  have hcs : cs π X = .app π (.psi π) pre R (info R).seq zero c :=
    cs_lim_app hX hsX hns hmk (fun σ hd => by
      rw [hr] at hd; cases hd; exact Or.inr (Or.inl hold))
  have hdom : dom (.Psi π X) = .omega := by
    rw [dom_psi, hcs]; simp only [SeqD.dom, hr, hlt, Bool.false_eq_true, ↓reduceIte]
  -- 塔
  obtain ⟨γ, hγdef⟩ : ∃ γ : Nat → Tm, γ = gam π (.M m) (.psi π) pre R (info R).seq c .zero := ⟨_, rfl⟩
  have hγ0 : γ 0 = kTop π m pre R (info R).seq := by rw [hγdef]; exact gam_K_zero hcan
  have hγS' : ∀ n, γ (n + 1) = col (.M m) (oadd (ofSummands pre) (fundBig R (γ n))) n := by
    intro n; rw [hγdef]; exact gam_K_succ hcan n
  have hfN : ∀ n, fundNat (.Psi π X) n = .Psi π (combine (.psi π) pre c .zero (fundBig R (γ n))) := by
    intro n; rw [fundNat_psi, hcs, hγdef]; exact nat_app_K hr hlt hcan n
  have hadj' : AdjOK π pre R (fundBig R (γ 0)) c := by rw [hγ0]; exact hadj
  -- `B ξ = pre ⊕ R[ξ]`
  have hxF : ∀ ξ, WNF ξ → Lt ξ (.M m) → WNF (fundBig R ξ) := fun ξ hξ hξM => hRP.nf ξ hξ hξM
  have hBF : ∀ ξ, WNF ξ → Lt ξ (.M m) → WNF (oadd (ofSummands pre) (fundBig R ξ)) :=
    fun ξ hξ hξM => wnf_oadd hPF (hxF ξ hξ hξM)
  have hBX : ∀ ξ, WNF ξ → Lt ξ (.M m) → Lt (oadd (ofSummands pre) (fundBig R ξ)) X := by
    intro ξ hξ hξM
    have := oadd_lt_oadd hPF (hxF ξ hξ hξM) hR.1 (hRP.lt ξ hξ hξM)
    rw [← hXe] at this; exact this
  have hXCM : inC X X (.M m) = true :=
    inC_mono X X _ X _ hP.Ca (fun v hv hvt => lt_transY (hX.of_mem_subs hv) ht hMF hvt htM)
      (fun _ _ h => h)
  have hXiF : ∀ ξ, WNF ξ → Lt ξ (.M m) → WNF (.Xi m (oadd (ofSummands pre) (fundBig R ξ))) := by
    intro ξ hξ hξM
    have hB := hBF ξ hξ hξM
    have hBS := lt_transY hB hX (WNF.succM hm) (hBX ξ hξ hξM) hXS
    refine WNF.mk_xi hm hB (ne_gt_of_le (Or.inr hBS)) ?_
    have htr := summand_inC_transfer hX hsX (hxF ξ hξ hξM)
      (fun v hv hne hlt' => hRi.gapP hR.2 ξ v hξ hξM hv hne hlt') (hRi.pos ξ hξ hξM) hXCM
    refine inC_oadd hPF (hxF ξ hξ hξM) ((inC_ofSummands pre).mpr (fun s hs =>
      htr s (by rw [hsX]; exact List.mem_append_left _ hs))) ?_
    by_cases hB0 : oadd (ofSummands pre) (fundBig R ξ) = .zero
    · have hx0 := (oadd_eq_zero hPF (hxF ξ hξ hξM) hB0).2
      rw [hx0]; exact inC_zero _ _
    · exact hRi.ub _ _ ξ hB hB0 (Cut.of_wnf hMF) hξ hξM (inC_kTerm _ _ _) (htr R hRX)
        (inC_of_lt_cut (Cut.of_wnf hMF) _ hξ hξM)
  have key : ∀ n, WNF (γ n) ∧ Lt (γ n) (.M m) := by
    intro n
    induction n with
    | zero => rw [hγ0]; exact ⟨hG0F, hG0M⟩
    | succ n ih =>
      have hle : leB (oadd (ofSummands pre) (fundBig R (γ n))) (succM m) = true :=
        le_leB (Or.inr (lt_transY (hBF _ ih.1 ih.2) hX (WNF.succM hm) (hBX _ ih.1 ih.2) hXS))
      rw [hγS' n, col_M_le hle]
      exact ⟨hXiF _ ih.1 ih.2, xi_lt_M _⟩
  have hγF : ∀ n, WNF (γ n) := fun n => (key n).1
  have hγM : ∀ n, Lt (γ n) (.M m) := fun n => (key n).2
  have hγS : ∀ n, γ (n + 1) = .Xi m (oadd (ofSummands pre) (fundBig R (γ n))) := fun n => by
    rw [hγS' n, col_M_le (le_leB (Or.inr (lt_transY (hBF _ (hγF n) (hγM n)) hX (WNF.succM hm)
      (hBX _ (hγF n) (hγM n)) hXS)))]
  have hγm : ∀ n, Lt (γ n) (γ (n + 1)) := by
    intro n
    have hy := hXiF _ (hγF n) (hγM n)
    rw [hγS n]
    refine coll_xi0 hy (γ n) (hγF n) ?_ (hγM n)
    have h1 := inC_of_oadd_right hPF (hxF _ (hγF n) (hγM n)) (xi_selfY hy)
    exact hRi.lo _ _ (γ n) (Cut.of_wnf hy) (hγF n) (hγM n) h1
  have hmono0 : ∀ n, Le (fundBig R (γ 0)) (fundBig R (γ n)) := by
    intro n
    rcases seq_mono_le hγF hγm (Nat.zero_le n) with e | h
    · rw [e]; exact Or.inl rfl
    · exact Or.inr (hRP.mono _ _ (hγF 0) (hγF n) h (hγM n))
  -- `t` の近似
  have hf : ∀ n, fundNat (.Psi π X) n = .Psi π (apx pre c (fundBig R (γ n))) := fun n => by
    rw [hfN n, combine_psi_zero pre hadj.cF (hxF _ (hγF n) (hγM n))]
  have hcore := fun (n : Nat) => approx_core (π := π) ht hsX hadj.cF hadj.cR (hxF _ (hγF n) (hγM n))
    (hRP.lt _ (hγF n) (hγM n))
    (fun v hv hne hlt' => hRi.gapP hR.2 (γ n) v (hγF n) (hγM n) hv hne hlt')
    (hRi.pos (γ n) (hγF n) (hγM n))
  have hAF : ∀ n, WNF (apx pre c (fundBig R (γ n))) := fun n => (hcore n).1
  have hA'F : ∀ n, WNF (oadd c (fundBig R (γ n))) := fun n => wnf_oadd hadj.cF (hxF _ (hγF n) (hγM n))
  have hAm : ∀ n, Lt (apx pre c (fundBig R (γ n))) (apx pre c (fundBig R (γ (n + 1)))) := fun n =>
    oadd_lt_oadd hPF (hA'F n) (hA'F (n + 1)) (oadd_lt_oadd hadj.cF (hxF _ (hγF n) (hγM n))
      (hxF _ (hγF _) (hγM _)) (hRP.mono _ _ (hγF n) (hγF _) (hγm n) (hγM _)))
  have hcutA : ∀ n, Cut (.Psi π (apx pre c (fundBig R (γ n)))) := fun n => cut_psi hπ hπT (hAF n)
  have hval : ∀ n, validR π (apx pre c (fundBig R (γ n))) = true := fun n =>
    hadj'.valid _ (hxF _ (hγF n) (hγM n)) (hmono0 n)
  have hA0s : ∀ n, apx pre c (fundBig R (γ (n + 1))) ≠ .zero := by
    intro n e
    have hx := hxF _ (hγF (n + 1)) (hγM (n + 1))
    have h1 := (oadd_eq_zero hadj.cF hx (oadd_eq_zero hPF (wnf_oadd hadj.cF hx) e).2).2
    have h2 := hRi.ge (γ (n + 1)) (hγF _) (hγM _)
    rw [h1] at h2
    have h3 : γ (n + 1) ≠ .zero := by rw [hγS n]; intro e; cases e
    rcases h2 with e' | h2
    · exact h3 e'
    · exact not_lt_zero _ h2
  -- 添字は近似の成分
  have hC : ∀ n, inC (γ n) (apx pre c (fundBig R (γ n)))
      (.Psi π (apx pre c (fundBig R (γ n)))) = true := by
    intro n
    induction n with
    | zero =>
      have hπC := tgt_inC_approx ht (hAF 0) (hval 0) (hcore 0).2.2.2.1
      have hπd : ¬ Lt π (.Psi π (apx pre c (fundBig R (γ 0)))) :=
        fun h => Lt.irrefl _ (below_lt_tgt hπ hπT π hπ h)
      have := hG0C _ _ (hcutA 0) (fr_inC_of_tgt hπ hπT (hAF 0) (hcutA 0) hπC hπd)
      rw [← hγ0] at this; exact this
    | succ n ih =>
      by_cases hlt' : Lt (γ (n + 1)) (.Psi π (apx pre c (fundBig R (γ (n + 1)))))
      · exact inC_of_lt_cut (hcutA (n + 1)) _ (hγF _) hlt'
      · have hγnC : inC (γ n) (apx pre c (fundBig R (γ (n + 1))))
            (.Psi π (apx pre c (fundBig R (γ (n + 1))))) = true :=
          inC_mono _ _ _ _ _ ih
            (fun v hv hvy => below_mono hπ hπT (hAF _) (hAF n) (Or.inr (hAm n))
              ((hγF n).of_mem_subs hv) hvy)
            (fun v hv hvA => lt_transY ((hγF n).of_mem_subs hv) (hAF n) (hAF _) hvA (hAm n))
        have hBnC : inC (oadd (ofSummands pre) (fundBig R (γ n))) (apx pre c (fundBig R (γ (n + 1))))
            (.Psi π (apx pre c (fundBig R (γ (n + 1))))) = true :=
          inC_oadd hPF (hxF _ (hγF n) (hγM n))
            ((inC_ofSummands pre).mpr (fun s hs =>
              (hcore (n + 1)).2.2.2.2 s (by rw [hsX]; exact List.mem_append_left _ hs)))
            (hRi.ub _ _ (γ n) (hAF _) (hA0s n) (hcutA _) (hγF n) (hγM n) (inC_kTerm _ _ _)
              ((hcore (n + 1)).2.2.2.2 R hRX) hγnC)
        have hBnlt : Lt (oadd (ofSummands pre) (fundBig R (γ n))) (apx pre c (fundBig R (γ (n + 1)))) :=
          lt_of_lt_of_leY (hBF _ (hγF n) (hγM n)) (hBF _ (hγF _) (hγM _)) (hAF _)
            (oadd_lt_oadd hPF (hxF _ (hγF n) (hγM n)) (hxF _ (hγF _) (hγM _))
              (hRP.mono _ _ (hγF n) (hγF _) (hγm n) (hγM _)))
            (oadd_le_oadd hPF (hxF _ (hγF _) (hγM _)) (hA'F _)
              (le_oadd_right hadj.cF (hxF _ (hγF _) (hγM _))))
        have h : inC (.Xi m (oadd (ofSummands pre) (fundBig R (γ n))))
            (apx pre c (fundBig R (γ (n + 1)))) (.Psi π (apx pre c (fundBig R (γ (n + 1))))) = true :=
          inC_xi_iff.mpr (Or.inr ⟨hBnC, hBnlt⟩)
        rw [← hγS n] at h
        exact h
  -- 上界
  have hub : ∀ g d, WNF g → g ≠ .zero → Cut d → inC (.Psi π X) g d = true → ¬ Lt (.Psi π X) d →
      inC (base (.M m)) g d = true ∧ ∀ n, inC (γ n) g d = true := by
    intro g d hg hg0 hd hCt hlt'
    rcases inC_psi_iff.mp hCt with h1 | ⟨hπC, hXC, hXg⟩
    · exact absurd h1 hlt'
    have hπd : ¬ Lt π d := fun h' => hlt' (hd _ _ ht hπ (lt_psi_targetY ht) h')
    have hRCg : inC R g d = true := inC_of_mem_summands hX hXC hRX
    refine ⟨inC_kTerm _ _ _, fun n => ?_⟩
    induction n with
    | zero =>
      have := hG0C g d hd (fr_inC_of_tgt hπ hπT hg hd hπC hπd)
      rw [← hγ0] at this; exact this
    | succ n ih =>
      rw [hγS n]
      by_cases hyd : Lt (.Xi m (oadd (ofSummands pre) (fundBig R (γ n)))) d
      · exact inC_of_lt_node (Or.inl ⟨_, _, rfl⟩) hyd
      · refine inC_xi_iff.mpr (Or.inr ⟨?_, lt_transY (hBF _ (hγF n) (hγM n)) hX hg
          (hBX _ (hγF n) (hγM n)) hXg⟩)
        exact inC_oadd hPF (hxF _ (hγF n) (hγM n))
          ((inC_ofSummands pre).mpr (fun s hs =>
            inC_of_mem_summands hX hXC (by rw [hsX]; exact List.mem_append_left _ hs)))
          (hRi.ub g d (γ n) hg hg0 hd (hγF n) (hγM n) (inC_kTerm _ _ _) hRCg ih)
  -- 目標の前線の元は塔の下：障害は塔の 1 段目未満
  have hs1 : ∀ s, kNeed m π (oadd (ofSummands pre) R) = some s → Lt s (γ 1) := by
    intro s hs
    rcases kTop_cases π m pre R (info R).seq with ⟨hN, -⟩ | ⟨s', hs', h⟩
    · rw [hs] at hN; cases hN
    · rw [hs] at hs'
      cases hs'
      rcases h with ⟨h0, hlt1⟩ | h0
      · rw [hγS 0, hγ0, h0]
        exact hlt1
      · have := hγm 0
        rw [hγ0, h0] at this
        exact this
  have hfrγ : ∀ e, e ∈ fr π π → ∃ k, Lt e (γ k) := by
    intro e he
    have heF := hπ.of_mem_subs (fr_spec he).1
    have heM : Lt e (.M m) := lt_transY heF hπ hMF (fr_spec he).2 hπM
    cases hN : kNeed m π (oadd (ofSummands pre) R) with
    | none =>
      have hKD := kNeed_none hm hπ hπM hN he (γ 0)
      rw [← hXe] at hKD
      exact kTop_hull hX hsX hRi hγF hγM hγm hγS (hγF 0) (hγm 0) e heF heM hKD
    | some s =>
      obtain ⟨e', he', hf'⟩ := kNeed_spec hN
      have he'F := hπ.of_mem_subs (fr_spec he').1
      have hsF := (kNd_true_spec hm he'F (lt_transY he'F hπ hMF (fr_spec he').2 hπM) hf').1
      have hKD := kNeed_KD hm hπ hπM hN he
      rw [← hXe] at hKD
      exact kTop_hull hX hsX hRi hγF hγM hγm hγS hsF (hs1 s hN) e heF heM hKD
  -- 目標は塔の下、したがって `t` も
  obtain ⟨N, hN⟩ := exists_bound (P := fun _ => True) hγF hγm (fr π π)
    (fun w hw => hπ.of_mem_subs (fr_spec hw).1) (fun w hw _ => hfrγ w hw)
  have hπγ : ∃ K, Lt π (γ K) := by
    by_cases hπN : Lt π (γ N)
    · exact ⟨N, hπN⟩
    have hCπ : inC π X (γ N) = true :=
      inC_of_fr_lt hπ hπ (hγF N) hX hX (tgt_inC_self hπ hπT hX (fun δ hδ => by
          obtain ⟨m', rfl⟩ := argR_some hδ; exact hP.act m' δ rfl))
        (le_of_not_ltY hπ (hγF N) hπN) (Or.inl rfl) (fun w hw => hN w hw trivial)
    exact xi_tower_hull_C hX hsX hRi hγF hγM hγm hγS
      (fun w hw h => lt_transY hw (hγF N) hMF h (hγM N)) (fun z _ h => ⟨N, h⟩) π hπ hπM hCπ
  obtain ⟨K, hK⟩ := hπγ
  have htK : Lt (.Psi π X) (γ K) := lt_transY ht hπ (hγF K) (lt_psi_targetY ht) hK
  -- 共終性
  have hcof : ∀ a a' N', WNF (.Psi π a) → WNF a' → Lt a X → summands a = pre ++ summands a' →
      Lt a' R → (∀ w, w ∈ fr π a → Lt w (.Psi π (apx pre c (fundBig R (γ N'))))) →
      ∃ k, Lt a' (fundBig R (γ k)) := by
    intro a a' N' hxF' ha' haX hsa ha'R _
    have haF := hxF'.psi.aF
    have hxt : Lt (.Psi π a) (.Psi π X) := lt_psi_psi_same.mpr haX
    have haC : inC a X (.Psi π X) = true := inC_mono a a _ X _ hxF'.psi.Ca
      (fun v hv hvx => lt_transY (haF.of_mem_subs hv) hxF' ht hvx hxt)
      (fun v hv hva => lt_transY (haF.of_mem_subs hv) haF hX hva haX)
    have ha'C : inC a' X (.Psi π X) = true := by
      rw [inC_iff_summandsW ha']
      intro s hs
      exact inC_of_mem_summands haF haC (by rw [hsa]; exact List.mem_append_right _ hs)
    have hg : ∀ g, g ∈ lfr (.M m) a' → ∃ k, Lt g (γ k) := fun g hg =>
      xi_tower_hull_C hX hsX hRi hγF hγM hγm hγS
        (fun w hw h => lt_transY hw ht hMF h htM)
        (fun z hz h => ⟨K, lt_transY hz ht (hγF K) h htK⟩) g (ha'.of_mem_subs (lfr_spec hg).1)
        (lfr_spec hg).2 (inC_lfr hMF ht (Or.inr htM) ha' ha'C hg)
    obtain ⟨M', hM'⟩ := exists_bound (P := fun _ => True) hγF hγm (lfr (.M m) a')
      (fun g hg' => ha'.of_mem_subs (lfr_spec hg').1) (fun g hg' _ => hg g hg')
    refine ⟨M' + 1, hRi.lclo a' (γ (M' + 1)) ha' ha'R (hγF _) ?_ (hγM _) (fun g hg' => ?_)⟩
    · rw [hγS M']; exact zero_lt (by intro e; cases e)
    · exact lt_transY (ha'.of_mem_subs (lfr_spec hg').1) (hγF M') (hγF _) (hM' g hg' trivial)
        (hγm M')
  refine ⟨fun _ => natInv_psi_idx_x0 ht hsX hRi hadj' γ hγF hγM hγm hmono0 hf hC
    (fun n => inC_kTerm _ _ _) hub hcof (fun g d n hg hg0 hd hCy hlt' => ?_),
    fun σ hd => by rw [hdom] at hd; cases hd⟩
  rcases inC_psi_iff.mp hCy with h1 | ⟨-, hAC, -⟩
  · exact absurd h1 hlt'
  refine ⟨inC_kTerm _ _ _, ?_⟩
  have hcR : Lt (oadd c (fundBig R (γ (n + 1)))) R :=
    oadd_lt_prin hadj.cF (hxF _ (hγF _) (hγM _)) hR.2 hadj.cR (hRP.lt _ (hγF _) (hγM _))
  obtain ⟨-, hyC⟩ := inC_oadd_pre hXn (hA'F (n + 1)) hcR hAC
  have hγ1C := hRi.lo g d (γ (n + 1)) hd (hγF _) (hγM _)
    (inC_of_oadd_right hadj.cF (hxF _ (hγF _) (hγM _)) hyC)
  by_cases hlt1 : Lt (γ (n + 1)) d
  · exact inC_of_lt_cut hd g (hγF n) (hd _ _ (hγF n) (hγF _) (hγm n) hlt1)
  · rw [hγS n] at hγ1C hlt1
    rcases inC_xi_iff.mp hγ1C with h1 | ⟨hBC, -⟩
    · exact absurd h1 hlt1
    obtain ⟨-, hxnC⟩ := inC_oadd_pre hXn (hxF _ (hγF n) (hγM n)) (hRP.lt _ (hγF n) (hγM n)) hBC
    exact hRi.lo g d (γ n) hd (hγF n) (hγM n) hxnC

end MahloOCF.FS
