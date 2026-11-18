import Mahlo.FS.Virt

/-! `M_m` への対角化のうち、近似の引数が `M_m⁺` 以上の場合（`kOld`）。

`t[n] = Ψ_π(pre ⊕ (c ⊕ R[γ_n]))`、添字は `γ_0 = 0`、`γ_{k+1} = Ξ_m(M_m⁺)`（引数がちょうど `M_m⁺`）か
`virtK m k`。近似の引数は `M_m⁺` 以上（`R > M_m⁺` なら `R[ξ] ≥ M_m⁺`（`lbS`））なので、2 段目以降は全て
`virtK` で、`M_m` 未満の標準形は全てその下にある（`virt_all`）。 -/

namespace MahloOCF.FS

open Tm

/-! ### 列の記述の評価（`kOld`） -/

theorem gam_O_zero {π : Tm} {m : Nat} {pre : List Tm} {R : Tm} {r : SeqD} {c P : Tm}
    (hcan : canonK (.M m) (.psi π) pre R = false)
    (hout : outsideMode π (.M m) (.psi π) pre R = true) :
    gam π (.M m) (.psi π) pre R r c P 0 = .zero := by
  simp only [gam, hcan, hout, Bool.false_eq_true, ↓reduceIte]

theorem gam_O_succ {π : Tm} {m : Nat} {pre : List Tm} {R : Tm} {r : SeqD} {c P : Tm}
    (hcan : canonK (.M m) (.psi π) pre R = false)
    (hout : outsideMode π (.M m) (.psi π) pre R = true) (k : Nat) :
    gam π (.M m) (.psi π) pre R r c P (k + 1) =
      col (.M m) (combine (.psi π) pre c P (r.big (gam π (.M m) (.psi π) pre R r c P k))) k := by
  simp only [gam, hcan, hout, Bool.false_eq_true, ↓reduceIte, argOf]

theorem nat_app_O {π : Tm} {m : Nat} {pre : List Tm} {R : Tm} {r : SeqD} {c : Tm}
    (hd : r.dom = .big (.M m)) (hlt : ltB (.M m) π = false)
    (hcan : canonK (.M m) (.psi π) pre R = false)
    (hout : outsideMode π (.M m) (.psi π) pre R = true) (n : Nat) :
    (SeqD.app π (.psi π) pre R r .zero c).nat n =
      .Psi π (combine (.psi π) pre c .zero (r.big (gam π (.M m) (.psi π) pre R r c .zero n))) := by
  simp only [SeqD.nat, hd, hlt, Bool.false_eq_true, ↓reduceIte, argOf, hcan, hout, Gen.ap]

theorem col_M_gt {m k : Nat} {δ : Tm} (h : leB δ (succM m) = false) : col (.M m) δ k = virtK m k := by
  simp only [col, h, Bool.false_eq_true, ↓reduceIte]

/-- `R` の共終数が `M_m` なら、塔の始点の置き換え（`outFix`）は働かない -/
theorem cs_lim_app_M {π X R c : Tm} {m : Nat} {pre : List Tm} (hX : WNF X)
    (hsX : summands X = pre ++ [R]) (hns : ¬ isSucc X = true)
    (hmk : mkApp π (.psi π) pre R (info R).seq zero zero =
      some (.app π (.psi π) pre R (info R).seq zero c))
    (hr : (info R).seq.dom = .big (.M m)) :
    cs π X = .app π (.psi π) pre R (info R).seq zero c := by
  rw [cs_lim_eq hX hsX hns, hmk, Option.map_some, Option.getD_some]
  simp only [outFix, hr]

/-! ### `kOld` の列の不変量 -/

theorem inv_psi_diag_KO {π X R : Tm} {m : Nat} {pre : List Tm} (ht : WNF (.Psi π X))
    (hsX : summands X = pre ++ [R]) (hns : ¬ isSucc X = true)
    (hRd : dom R = .big (.M m)) (hRi : BigInv R (.M m)) (hMπ : ¬ Lt (.M m) π)
    (hold : kOld m pre R = true) : Inv (.Psi π X) := by
  have hP := ht.psi
  have hX := hP.aF
  have hπ := hP.piF
  have hπT := hP.tgt
  have hXn : NFL (pre ++ [R]) := by rw [← hsX]; exact nfl_summands hX
  have hpreN := nfl_append_left hXn
  have hPF := wnf_ofSummands hpreN
  have hR := hXn.1 R (by simp)
  have hR0 : R ≠ .zero := by intro e; rw [e] at hR; cases hR.2
  have hRX : R ∈ summands X := by rw [hsX]; simp
  have hRP := hRi.props
  have hMF : WNF (.M m) := hRP.σF
  have hm : 1 ≤ m := hMF.M
  have hSF := WNF.succM hm
  have hπM : Lt π (.M m) := by
    rcases triY hπ hMF with h | e | h
    · exact h
    · exact absurd e (hπT.notM m)
    · exact absurd h hMπ
  have hr : (info R).seq.dom = .big (.M m) := hRd
  have hlt : ltB (.M m) π = false := by
    cases e : ltB (.M m) π with
    | false => rfl
    | true => exact absurd (ltB_iff.mp e) hMπ
  have hcan : canonK (.M m) (.psi π) pre R = false := by
    show (!kOld m pre R) = false
    rw [hold]; rfl
  have hout : outsideMode π (.M m) (.psi π) pre R = true := hold
  have hXe : X = oadd (ofSummands pre) R := eq_oadd_of_summands hX hsX
  have hSX : Le (succM m) X := by
    have h1 : leB (succM m) X = true := by rw [hXe]; exact hold
    exact le_of_ne_gtY hSF hX (leB_iff.mp h1)
  -- 調整 `c`
  have hk : kAdj π π (.psi π) pre R (info R).seq = .zero := by
    unfold kAdj; rw [hr]; simp only [hcan, Bool.and_false, Bool.false_eq_true, ↓reduceIte]
  have hfirst : (info R).seq.first = fundBig R .zero := by unfold SeqD.first; rw [hr]; rfl
  obtain ⟨c, hmk, hadj⟩ := mkApp_plain ht hsX hns hk
    (by rw [hfirst]; exact hRP.nf .zero WNF.zero hRP.pos)
  rw [hfirst] at hadj
  have hcs : cs π X = .app π (.psi π) pre R (info R).seq zero c := cs_lim_app_M hX hsX hns hmk hr
  have hdom : dom (.Psi π X) = .omega := by
    rw [dom_psi, hcs]; simp only [SeqD.dom, hr, hlt, Bool.false_eq_true, ↓reduceIte]
  -- 近似の引数
  have hxF : ∀ ξ, WNF ξ → Lt ξ (.M m) → WNF (fundBig R ξ) := fun ξ hξ hξM => hRP.nf ξ hξ hξM
  have hAF' : ∀ ξ, WNF ξ → Lt ξ (.M m) → WNF (apx pre c (fundBig R ξ)) := fun ξ hξ hξM =>
    wnf_oadd hPF (wnf_oadd hadj.cF (hxF ξ hξ hξM))
  have hAmono : ∀ ξ η, WNF ξ → WNF η → Lt ξ η → Lt η (.M m) →
      Lt (apx pre c (fundBig R ξ)) (apx pre c (fundBig R η)) := by
    intro ξ η hξ hη hξη hηM
    have hξM := lt_transY hξ hη hMF hξη hηM
    exact oadd_lt_oadd hPF (wnf_oadd hadj.cF (hxF ξ hξ hξM)) (wnf_oadd hadj.cF (hxF η hη hηM))
      (oadd_lt_oadd hadj.cF (hxF ξ hξ hξM) (hxF η hη hηM) (hRP.mono ξ η hξ hη hξη hηM))
  -- 近似の引数は `M_m⁺` 以上
  have lbA : ∀ ξ, WNF ξ → Lt ξ (.M m) → Le (succM m) (apx pre c (fundBig R ξ)) := by
    intro ξ hξ hξM
    have hx := hxF ξ hξ hξM
    have hA := hAF' ξ hξ hξM
    have hA'F := wnf_oadd hadj.cF hx
    cases pre with
    | nil =>
      have hXR : X = R := by rw [hXe]; exact zero_oadd hR.1
      have hSR : Lt (succM m) R := by
        rcases (show Le (succM m) R by rw [← hXR]; exact hSX) with e | h
        · exfalso
          have h2 : dom (Tm.Om (.plus (.M m) one)) = .big (.M m) := by rw [← hRd, ← e]; rfl
          rw [dom_om_reg (c := .plus (.M m) one) (Or.inr rfl)] at h2
          cases h2
        · exact h
      have h1 := hRi.lbS m rfl hSR ξ hξ hξM
      have h2 : Le (fundBig R ξ) (apx [] c (fundBig R ξ)) :=
        le_transY hx hA'F hA (le_oadd_right hadj.cF hx) (le_oadd_right hPF hA'F)
      exact le_transY hSF hx hA h1 h2
    | cons a l =>
      have hsP : summands (ofSummands (a :: l)) = a :: l := summands_ofSummands _ (nfl_principal hpreN)
      have haN := hpreN.1 a List.mem_cons_self
      have hsX' : summands X = a :: (l ++ [R]) := by rw [hsX]; rfl
      have h1 : Le (succM m) a := le_of_not_ltY haN.1 hSF (fun h' =>
        not_lt_of_leY hSF hX hSX (lt_of_head_lt rfl hsX' ((lt_principal_iff haN.2 rfl).mp h')))
      have h2 : Le a (ofSummands (a :: l)) := head_leY hPF hsP
      exact le_transY hSF haN.1 hA h1 (le_transY haN.1 hPF hA h2 (le_oadd_leftW hPF hA'F))
  -- 塔
  obtain ⟨γ, hγdef⟩ : ∃ γ : Nat → Tm, γ = gam π (.M m) (.psi π) pre R (info R).seq c .zero := ⟨_, rfl⟩
  have hγ0 : γ 0 = .zero := by rw [hγdef]; exact gam_O_zero hcan hout
  have hγS0 : ∀ n, γ (n + 1) = col (.M m) (combine (.psi π) pre c .zero (fundBig R (γ n))) n := by
    intro n; rw [hγdef]; exact gam_O_succ hcan hout n
  have hfN : ∀ n, fundNat (.Psi π X) n = .Psi π (combine (.psi π) pre c .zero (fundBig R (γ n))) := by
    intro n; rw [fundNat_psi, hcs, hγdef]; exact nat_app_O hr hlt hcan hout n
  -- 1 段の形
  have form : ∀ n, WNF (γ n) → Lt (γ n) (.M m) →
      (γ (n + 1) = .Xi m (succM m) ∧ apx pre c (fundBig R (γ n)) = succM m) ∨
      (γ (n + 1) = virtK m n ∧ Lt (succM m) (apx pre c (fundBig R (γ n)))) := by
    intro n hγ hγM
    have hx := hxF _ hγ hγM
    have hA := hAF' _ hγ hγM
    have hcol : γ (n + 1) = col (.M m) (apx pre c (fundBig R (γ n))) n := by
      rw [hγS0 n, combine_psi_zero pre hadj.cF hx]
    rw [hcol]
    rcases lbA _ hγ hγM with e | h
    · refine Or.inl ⟨?_, e.symm⟩
      rw [← e]
      exact col_M_le (le_leB (Or.inl rfl))
    · refine Or.inr ⟨col_M_gt ?_, h⟩
      cases e : leB (apx pre c (fundBig R (γ n))) (succM m) with
      | false => rfl
      | true => exact absurd h (not_lt_of_leY hA hSF (le_of_ne_gtY hA hSF (leB_iff.mp e)))
  have key : ∀ n, WNF (γ n) ∧ Lt (γ n) (.M m) := by
    intro n
    induction n with
    | zero => rw [hγ0]; exact ⟨WNF.zero, zero_lt (by intro e; cases e)⟩
    | succ n ih =>
      rcases form n ih.1 ih.2 with ⟨e, -⟩ | ⟨e, -⟩
      · rw [e]; exact ⟨wnf_xiS hm, xiS_lt_M⟩
      · rw [e]; exact ⟨wnf_virtK hm n, virtK_lt_M n⟩
  have hγF : ∀ n, WNF (γ n) := fun n => (key n).1
  have hγM : ∀ n, Lt (γ n) (.M m) := fun n => (key n).2
  -- 単調性
  have hγm : ∀ n, Lt (γ n) (γ (n + 1)) := by
    intro n
    induction n with
    | zero =>
      rw [hγ0]
      rcases form 0 (hγF 0) (hγM 0) with ⟨e, -⟩ | ⟨e, -⟩
      · rw [e]; exact zero_lt (by intro e'; cases e')
      · rw [e, virtK_eq]; exact zero_lt (by intro e'; cases e')
    | succ n ih =>
      have hAA := hAmono _ _ (hγF n) (hγF (n + 1)) ih (hγM (n + 1))
      have hS : Lt (succM m) (apx pre c (fundBig R (γ (n + 1)))) :=
        lt_of_le_of_ltY hSF (hAF' _ (hγF n) (hγM n)) (hAF' _ (hγF _) (hγM _))
          (lbA _ (hγF n) (hγM n)) hAA
      have e2 : γ (n + 1 + 1) = virtK m (n + 1) := by
        rcases form (n + 1) (hγF _) (hγM _) with ⟨-, e⟩ | ⟨e, -⟩
        · rw [e] at hS; exact absurd hS (Lt.irrefl _)
        · exact e
      rw [e2]
      rcases form n (hγF n) (hγM n) with ⟨e, -⟩ | ⟨e, -⟩
      · rw [e]; exact xiS_lt_virtK hm _
      · rw [e]; exact virtK_mono hm n
  -- `M_m⁺ < A_{n+1}`、2 段目以降は `virtK`
  have hSA : ∀ n, Lt (succM m) (apx pre c (fundBig R (γ (n + 1)))) := fun n =>
    lt_of_le_of_ltY hSF (hAF' _ (hγF n) (hγM n)) (hAF' _ (hγF _) (hγM _)) (lbA _ (hγF n) (hγM n))
      (hAmono _ _ (hγF n) (hγF (n + 1)) (hγm n) (hγM (n + 1)))
  have hγ2 : ∀ n, γ (n + 2) = virtK m (n + 1) := by
    intro n
    have hS := hSA n
    rcases form (n + 1) (hγF _) (hγM _) with ⟨-, e⟩ | ⟨e, -⟩
    · rw [e] at hS; exact absurd hS (Lt.irrefl _)
    · exact e
  have hγC : ∀ n g d, WNF g → Lt (succM m) g → inC (γ (n + 1)) g d = true := by
    intro n g d hg hSg
    rcases form n (hγF n) (hγM n) with ⟨e, -⟩ | ⟨e, -⟩
    · rw [e]; exact inC_xiS hm hg hSg
    · rw [e]; exact inC_virtK hm hg hSg n
  -- `t` の近似
  have hf : ∀ n, fundNat (.Psi π X) n = .Psi π (apx pre c (fundBig R (γ n))) := fun n => by
    rw [hfN n, combine_psi_zero pre hadj.cF (hxF _ (hγF n) (hγM n))]
  have hC : ∀ n, inC (γ n) (apx pre c (fundBig R (γ n)))
      (.Psi π (apx pre c (fundBig R (γ n)))) = true := by
    intro n
    cases n with
    | zero => rw [hγ0]; exact inC_zero _ _
    | succ n => exact hγC n _ _ (hAF' _ (hγF _) (hγM _)) (hSA n)
  have hub : ∀ g d, WNF g → g ≠ .zero → Cut d → inC (.Psi π X) g d = true → ¬ Lt (.Psi π X) d →
      inC (base (.M m)) g d = true ∧ ∀ n, inC (γ n) g d = true := by
    intro g d hg _ _ hCt hlt'
    rcases inC_psi_iff.mp hCt with h1 | ⟨-, -, hXg⟩
    · exact absurd h1 hlt'
    have hSg : Lt (succM m) g := lt_of_le_of_ltY hSF hX hg hSX hXg
    refine ⟨inC_kTerm _ _ _, fun n => ?_⟩
    cases n with
    | zero => rw [hγ0]; exact inC_zero _ _
    | succ n => exact hγC n g d hg hSg
  -- 共終性
  have hcof : ∀ a a' N', WNF (.Psi π a) → WNF a' → Lt a X → summands a = pre ++ summands a' →
      Lt a' R → (∀ w, w ∈ fr π a → Lt w (.Psi π (apx pre c (fundBig R (γ N'))))) →
      ∃ k, Lt a' (fundBig R (γ k)) := by
    intro a a' N' _ ha' _ _ ha'R _
    obtain ⟨N, hN⟩ := exists_bound (P := fun _ => True) (wnf_virtK hm) (virtK_mono hm)
      (lfr (.M m) a') (fun g hg => ha'.of_mem_subs (lfr_spec hg).1)
      (fun g hg _ => virt_all hm g (ha'.of_mem_subs (lfr_spec hg).1) (lfr_spec hg).2)
    refine ⟨N + 2, hRi.lclo a' (γ (N + 2)) ha' ha'R (hγF _) ?_ (hγM _) (fun g hg => ?_)⟩
    · rw [hγ2 N, virtK_eq]; exact zero_lt (by intro e; cases e)
    · rw [hγ2 N]
      exact lt_transY (ha'.of_mem_subs (lfr_spec hg).1) (wnf_virtK hm N) (wnf_virtK hm _)
        (hN g hg trivial) (virtK_mono hm N)
  refine ⟨fun _ => natInv_psi_idx ht hsX hRi hadj γ hγF hγM hγm hf hC
    (fun n => inC_kTerm _ _ _) hub hcof (fun g d n hg _ _ hCy hlt' => ?_),
    fun σ hd => by rw [hdom] at hd; cases hd⟩
  rcases inC_psi_iff.mp hCy with h1 | ⟨-, -, hAg⟩
  · exact absurd h1 hlt'
  have hSg : Lt (succM m) g := lt_transY hSF (hAF' _ (hγF _) (hγM _)) hg (hSA n) hAg
  refine ⟨inC_kTerm _ _ _, ?_⟩
  cases n with
  | zero => rw [hγ0]; exact inC_zero _ _
  | succ n => exact hγC n g d hg hSg

/-! ### `M_m` への対角化 -/

/-- `M_m` への対角化の列の不変量（`canonK`・`kOld`） -/
theorem psiDiagM_proof : PsiDiagM := by
  intro π X R m pre ht hsX hns hRd hRi hMπ _
  cases hold : kOld m pre R with
  | true => exact inv_psi_diag_KO ht hsX hns hRd hRi hMπ hold
  | false => exact inv_psi_diag_K ht hsX hns hRd hRi hMπ hold

end MahloOCF.FS
