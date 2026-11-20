import Mahlo.FS.BachFloor

/-! `M_m` への対角化（`R` の共終数が `M_m`、`π ≤ M_m`）の `BInv`。

`t[n] = Ψ_π(pre ⊕ (c ⊕ R[γ_n]))`。塔 `γ` の隣り合う項の区間の下界を示し、`R` の区間の下界の移送と
崩壊の持ち上げ（`lbi_psi_apx`）で列の梯子を得る。
* `kOld`（`pre ⊕ R ≥ M_m⁺`）：`γ = 0, Ξ_m(M_m⁺) か virtK 0, virtK 1, …`（種 `Ξ_m(M_m⁺)` の仮想的な塔）。
* `canonK`：`γ_{k+1} = Ξ_m(pre ⊕ R[γ_k])`、始点は `0` か障害 `s`（`Ξ_m(ζ)` か `Ψ_{Ξ_m(ζ)}(a)`、`ζ ≥ X`）。 -/

namespace MahloOCF.FS

open Tm

/-! ### 仮想的な塔（種 `Ξ_m(M_m⁺)`） -/

theorem binv_succM {m : Nat} (hm : 1 ≤ m) : BInv (succM m) := by
  have hSF := WNF.succM hm
  refine binv_reg hSF (IsRegY.tgt (succM_tgt m)) ?_ ?_
  · show (info (succM m)).seq.dom = _; rw [info_seq_succM]; rfl
  · intro ξ; show (info (succM m)).seq.big ξ = _; rw [info_seq_succM]; rfl

/-- 仮想的な崩壊の引数は `virtE ⊕ Ξ_m(M_m⁺)` -/
theorem virtA_eq {m : Nat} (hm : 1 ≤ m) (k : Nat) :
    virtA m k = oadd (virtE m k) (.Xi m (succM m)) := by
  have hPF := wnf_xiS hm
  have hMF := WNF.M' hm
  have hHhi : ∀ u, u ∈ summands (oadd (ofSummands []) (virtE m k)) → ¬ Lt u (.M m) := by
    intro u hu; rw [oadd_nil (virtE_F hm k)] at hu; exact virtE_high hm k u hu
  have h := xa_eq_high (nfl_S m hm) (virtE_F hm k) (virtE_lt hm k) hPF rfl xiS_lt_M hMF hHhi
  rw [oadd_nil (virtE_F hm k)] at h
  show nsum (virtE m k) (.Xi m (succM m)) = _
  rw [nsum_comm (virtE_F hm k) hPF, ← h]
  show nsum (Tm.Xi m (succM m)) (virtE m k) = oadd (ofSummands []) (nsum (Tm.Xi m (succM m)) (virtE m k))
  rw [oadd_nil (wnf_nsum hPF (virtE_F hm k))]

theorem virtK_eq' {m : Nat} (hm : 1 ≤ m) (k : Nat) :
    virtK m k = .Xi m (oadd (virtE m k) (.Xi m (succM m))) := by
  rw [virtK_eq, virtA_eq hm k]

/-- `Ξ_m(M_m⁺)` から `virtK m k` まで -/
theorem lbi_xiS_virtK {m : Nat} (hm : 1 ≤ m) (k : Nat) : LBI (.Xi m (succM m)) (virtK m k) := by
  have hPF := wnf_xiS hm
  have hy : WNF (.Xi m (oadd (virtE m k) (.Xi m (succM m)))) := by
    rw [← virtK_eq' hm k]; exact wnf_virtK hm k
  have hA := hy.xi.2.1
  have hAS : Lt (oadd (virtE m k) (.Xi m (succM m))) (succM m) := by
    rw [← virtA_eq hm k]; exact virtA_lt hm k
  rw [virtK_eq' hm k]
  refine lbi_xi_inv_hull hPF hy hAS (fun d hd hPd => ?_)
  have hE0 : Lt .zero (virtE m k) :=
    lt_of_lt_of_leY WNF.zero (wnf_psi0M hm) (virtE_F hm k) (zero_lt (by intro e; cases e))
      (le_oadd_leftW (wnf_psi0M hm) (virtG_F hm k))
  have hEA : Le (virtE m k) (oadd (virtE m k) (.Xi m (succM m))) := le_oadd_leftW (virtE_F hm k) hPF
  have h0 : Lt .zero (oadd (virtE m k) (.Xi m (succM m))) :=
    lt_of_lt_of_leY WNF.zero (virtE_F hm k) hA hE0 hEA
  exact inC_oadd (virtE_F hm k) hPF
    (inC_virtE hm h0 k (fun j hj => lt_of_lt_of_leY (virtE_F hm j) (virtE_F hm k) hA
      (virtE_lt_of hm hj) hEA))
    (inC_of_lt_cut (Cut.of_wnf hd) _ hPF hPd)

/-- 仮想的な塔の隣り合う項 -/
theorem lbi_virtK {m : Nat} (hm : 1 ≤ m) (k : Nat) : LBI (virtK m k) (virtK m (k + 1)) := by
  have hSF := WNF.succM hm
  have hPF := wnf_xiS hm
  have hS := binv_succM hm
  have hSS := binv_SS hm hS
  have hy : ∀ j, WNF (.Xi m (oadd (virtE m j) (.Xi m (succM m)))) := fun j => by
    rw [← virtK_eq' hm j]; exact wnf_virtK hm j
  have hAS : ∀ j, Lt (oadd (virtE m j) (.Xi m (succM m))) (succM m) := fun j => by
    rw [← virtA_eq hm j]; exact virtA_lt hm j
  have hPL : LBI (.Xi m (succM m)) (.Xi m (oadd (virtE m k) (.Xi m (succM m)))) := by
    rw [← virtK_eq' hm k]; exact lbi_xiS_virtK hm k
  rw [virtK_eq' hm k, virtK_eq' hm (k + 1)]
  exact lbi_seeded (virtE_F hm k) (virtE_F hm (k + 1)) hPF rfl (one_lt_xi hPF) xiS_lt_M
    (virtE_high hm k) (virtE_high hm (k + 1)) (Or.inr (virtE_mono hm k)) (lbi_virtE hm hS hSS k)
    (hy k) (hy (k + 1)) (hAS (k + 1)) hSF (xiClosed_xi hPF) (hAS (k + 1)) hPL
    (fun f hf => by rw [fr_virtE hm k f hf]; exact one_lt_xi hPF)
    (fun f hf => by rw [fr_virtE hm (k + 1) f hf]; exact one_lt_xi hPF)

/-! ### `kOld` -/

theorem binv_psi_diag_KO {π X R : Tm} {m : Nat} {pre : List Tm} (ht : WNF (.Psi π X))
    (hsX : summands X = pre ++ [R]) (hns : ¬ isSucc X = true)
    (hRd : dom R = .big (.M m)) (hRb : BInv R) (hMπ : ¬ Lt (.M m) π)
    (hold : kOld m pre R = true) : BInv (.Psi π X) := by
  have hP := ht.psi
  have hX := hP.aF
  have hπ := hP.piF
  have hπT := hP.tgt
  have hXn : NFL (pre ++ [R]) := by rw [← hsX]; exact nfl_summands hX
  have hpreN := nfl_append_left hXn
  have hPF := wnf_ofSummands hpreN
  have hR := hXn.1 R (by simp)
  have hRi := (inv_of R hR.1).2 (.M m) hRd
  have hRP := hRi.props
  have hMF : WNF (.M m) := hRP.σF
  have hm : 1 ≤ m := hMF.M
  have hSF := WNF.succM hm
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
  have hfirst : (info R).seq.first = fundBig R .zero := by unfold SeqD.first; rw [hr]; rfl
  obtain ⟨c, hmk, hadj⟩ := mkApp_plain ht hsX hns ((info R).seq.first)
  rw [hfirst] at hadj
  have hcS := mkApp_shape hπ hmk
  have hcs : cs π X = .app π (.psi π) pre R (info R).seq zero c := cs_lim_app_M hX hsX hns hmk hr
  have hdom : dom (.Psi π X) = .omega := by
    rw [dom_psi, hcs]; simp only [SeqD.dom, hr, hlt, Bool.false_eq_true, ↓reduceIte]
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
  have hSA : ∀ n, Lt (succM m) (apx pre c (fundBig R (γ (n + 1)))) := fun n =>
    lt_of_le_of_ltY hSF (hAF' _ (hγF n) (hγM n)) (hAF' _ (hγF _) (hγM _)) (lbA _ (hγF n) (hγM n))
      (hAmono _ _ (hγF n) (hγF (n + 1)) (hγm n) (hγM (n + 1)))
  have hγ2 : ∀ n, γ (n + 2) = virtK m (n + 1) := by
    intro n
    have hS := hSA n
    rcases form (n + 1) (hγF _) (hγM _) with ⟨-, e⟩ | ⟨e, -⟩
    · rw [e] at hS; exact absurd hS (Lt.irrefl _)
    · exact e
  -- 塔の隣り合う項の区間の下界
  have hlad : ∀ n, LBI (γ n) (γ (n + 1)) := by
    intro n
    cases n with
    | zero => rw [hγ0]; exact lbi_zero _
    | succ n =>
      show LBI (γ (n + 1)) (γ (n + 2))
      rw [hγ2 n]
      cases n with
      | zero =>
        rcases form 0 (hγF 0) (hγM 0) with ⟨e, -⟩ | ⟨e, -⟩
        · rw [e]; exact lbi_xiS_virtK hm 1
        · rw [e]; exact lbi_virtK hm 0
      | succ k => rw [hγ2 k]; exact lbi_virtK hm (k + 1)
  have hadm : ∀ n, γ n = .zero ∨ (isPrincipal (γ n) = true ∧ Lt (base (.M m)) (γ n)) := by
    intro n
    cases n with
    | zero => exact Or.inl hγ0
    | succ n =>
      right
      rcases form n (hγF n) (hγM n) with ⟨e, -⟩ | ⟨e, -⟩
      · rw [e]; exact ⟨rfl, floorLev_lt_xi (wnf_xiS hm)⟩
      · rw [e, virtK_eq]
        exact ⟨rfl, floorLev_lt_xi (by rw [← virtK_eq]; exact wnf_virtK hm n)⟩
  have hRL : ∀ n, LBI (fundBig R (γ n)) (fundBig R (γ (n + 1))) := fun n =>
    hRb.big (.M m) hRd (γ n) (γ (n + 1)) (hγF n) (hγF _) (Or.inr (hγm n)) (hγM _) (hadm n) (hlad n)
  have hf : ∀ n, fundNat (.Psi π X) n = .Psi π (apx pre c (fundBig R (γ n))) := fun n => by
    rw [hfN n, combine_psi_zero pre hadj.cF (hxF _ (hγF n) (hγM n))]
  have htP := (props_all _ ht).1 hdom
  refine ⟨fun _ n => ?_, fun σ hd => by rw [hdom] at hd; cases hd⟩
  have hA := htP.nf n
  have hA' := htP.nf (n + 1)
  rw [hf] at hA hA' ⊢
  rw [hf]
  exact lbi_psi_apx ht hsX hadj.cF hadj.cR hcS (hxF _ (hγF n) (hγM n)) (hxF _ (hγF _) (hγM _))
    (Or.inr (hRP.mono _ _ (hγF n) (hγF _) (hγm n) (hγM _))) (hRP.lt _ (hγF _) (hγM _)) (hRL n) hA hA'


/-! ### 障害の形 -/

/-- 障害の形：`Ξ_m(ζ)` か `Ψ_{Ξ_m(ζ)}(a)`（`ζ ≥ X`） -/
def KForm (m : Nat) (X u : Tm) : Prop :=
  (∃ ζ, u = .Xi m ζ ∧ ¬ Lt ζ X) ∨ (∃ ζ a, u = .Psi (.Xi m ζ) a ∧ ¬ Lt ζ X)

/-- `C(d, Ψ_{Ξ_m(d)}(a))`（`d < X`）に入る障害は `Ψ_{Ξ_m(d)}(a)` 未満 -/
theorem kForm_lt_of_inC {m : Nat} {X d a u : Tm} (hX : WNF X) (hp : WNF (.Psi (.Xi m d) a))
    (hdX : Lt d X) (hu : WNF u) (hK : KForm m X u) (hC : inC u d (.Psi (.Xi m d) a) = true) :
    Lt u (.Psi (.Xi m d) a) := by
  have hdF := hp.psi.piF.xi.2.1
  by_cases hlt : Lt u (.Psi (.Xi m d) a)
  · exact hlt
  exfalso
  rcases hK with ⟨ζ, rfl, hζX⟩ | ⟨ζ, b, rfl, hζX⟩
  · rcases inC_xi_iff.mp hC with h | ⟨-, hζd⟩
    · exact hlt h
    · exact hζX (lt_transY hu.xi.2.1 hdF hX hζd hdX)
  · rcases inC_psi_iff.mp hC with h | ⟨hκC, -, -⟩
    · exact hlt h
    · have hκF := hu.psi.piF
      rcases inC_xi_iff.mp hκC with h' | ⟨-, hζd⟩
      · exact hlt (lt_transY hu hκF hp (lt_psi_targetY hu) h')
      · exact hζX (lt_transY hκF.xi.2.1 hdF hX hζd hdX)

/-- `ζ` の中に見える `M_m` 未満の節点は `Ξ_m(ζ)` 未満 -/
theorem selfVis_lt_xi {m : Nat} {ζ u : Tm} (hy : WNF (.Xi m ζ)) (hu : WNF u) (huM : Lt u (.M m))
    (hv : selfVis u ζ = true) : Lt u (.Xi m ζ) := by
  obtain ⟨f, hf, huf⟩ := selfVis_fr hu huM hy.xi.2.1 hv
  exact lt_of_le_of_ltY hu (fr_elem hy.xi.2.1 hf).1 hy huf (fr_lt_xi hy hf)

/-- 塔の障害の探索の結果の形 -/
theorem kNd_form {m : Nat} {X : Tm} (hm : 1 ≤ m) (hX : WNF X) : ∀ (n : Nat) (top : Bool) (z u : Tm),
    2 * z.size + (if top then 0 else 1) ≤ n → WNF z → (top = true → Lt z (.M m)) →
    kNd m X top z = some u → KForm m X u := by
  have hMF : WNF (.M m) := WNF.M' hm
  intro n
  induction n with
  | zero =>
    intro top z u hn
    have := Tm.size_pos z
    exfalso
    cases top <;> simp only [↓reduceIte, Bool.false_eq_true] at hn <;> omega
  | succ n ih =>
    intro top z u hn hz hzM h
    cases top with
    | true =>
      have hzM' := hzM rfl
      simp only [↓reduceIte, Nat.add_zero] at hn
      cases z with
      | zero => rw [kNd_t_zero] at h; cases h
      | M j => rw [kNd_t_M] at h; cases h
      | plus a b =>
        rw [kNd_t_plus] at h
        obtain ⟨ha, hb, -, -⟩ := hz.plus
        simp only [Tm.size] at hn
        rcases maxOpt_cases h with h' | h'
        · exact ih true a u (by simp only [↓reduceIte]; omega) ha
            (fun _ => lt_transY ha hz hMF (lt_plus_leftY hz) hzM') h'
        · exact ih true b u (by simp only [↓reduceIte]; omega) hb
            (fun _ => lt_transY hb hz hMF (lt_plus_rightY hz) hzM') h'
      | Om e =>
        rw [kNd_t_om] at h
        simp only [Tm.size] at hn
        exact ih true e u (by simp only [↓reduceIte]; omega) hz.om.1
          (fun _ => lt_transY hz.om.1 hz hMF (lt_om_selfY hz) hzM') h
      | Psi ρ a =>
        rw [kNd_t_psi] at h
        have hρF := hz.psi.piF
        simp only [Tm.size] at hn
        have hρM := tgt_lt_M_of_psi hm hz hzM'
        cases hρ : kNd m X true ρ with
        | none => rw [hρ] at h; cases h
        | some u' =>
          rw [hρ] at h
          simp only [Option.some.injEq] at h
          split at h
          · subst h
            exact ih true ρ u' (by simp only [↓reduceIte]; omega) hρF (fun _ => hρM) hρ
          · rename_i hnlt
            subst h
            have hge : ¬ Lt u' (.Psi ρ a) := fun h' => hnlt (ltB_iff.mpr h')
            rcases hz.psi.tgt with e | ⟨c, e, hcs⟩ | ⟨j, d, e⟩
            · subst e; rw [kNd_t_om, kNd_t_zero] at hρ; cases hρ
            · subst e
              exfalso
              have hcF := hρF.om.1
              have hcM : Lt c (.M m) := lt_transY hcF hρF hMF (lt_om_selfY hρF) hρM
              rw [kNd_t_om] at hρ
              obtain ⟨hu'F, -, -, hu'c⟩ := kNd_true_spec hm hcF hcM hρ
              exact hge (lt_of_le_of_ltY hu'F hcF hz hu'c (cxY hz hcs))
            · subst e
              rw [kNd_t_xi] at hρ
              split at hρ
              · rename_i hjm
                have hmj : m = j := hjm.symm
                subst hmj
                split at hρ
                · rename_i hdX
                  exfalso
                  have hdF := hρF.xi.2.1
                  cases hd : kNd m X false d with
                  | none => rw [hd] at hρ; cases hρ
                  | some u'' =>
                    rw [hd] at hρ
                    simp only [Option.some.injEq] at hρ
                    obtain ⟨hu''F, hv, hu''M⟩ := kNd_false_spec hm hdF hd
                    have hu''y : Lt u'' (.Xi m d) := selfVis_lt_xi hρF hu''F hu''M hv
                    have hρe : u' = u'' := by rw [← hρ]; simp [ltB_iff.mpr hu''y]
                    subst hρe
                    have hK'' := ih false d u' (by
                      simp only [Bool.false_eq_true, ↓reduceIte]; simp only [Tm.size] at hn; omega)
                      hdF (fun e => by cases e) hd
                    obtain ⟨-, hdC⟩ := (baseOf_xi_iff m d _).mp (base_selfY hz)
                    have hu'C := inC_of_selfVis hu''F (Cut.of_wnf hz) hdF hv hdC
                    exact hge (kForm_lt_of_inC hX hz (ltB_iff.mp hdX) hu''F hK'' hu'C)
                · rename_i hdX
                  exact Or.inr ⟨d, a, rfl, fun h' => hdX (ltB_iff.mpr h')⟩
              · cases hρ
      | Xi j ζ =>
        rw [kNd_t_xi] at h
        have hζF := hz.xi.2.1
        simp only [Tm.size] at hn
        split at h
        · rename_i hjm
          have hmj : m = j := hjm.symm
          subst hmj
          split at h
          · cases hζ : kNd m X false ζ with
            | none => rw [hζ] at h; cases h
            | some u'' =>
              rw [hζ] at h
              simp only [Option.some.injEq] at h
              obtain ⟨hu''F, hv, hu''M⟩ := kNd_false_spec hm hζF hζ
              have hlt := selfVis_lt_xi hz hu''F hu''M hv
              have e : u = u'' := by rw [← h]; simp [ltB_iff.mpr hlt]
              subst e
              exact ih false ζ u (by simp only [Bool.false_eq_true, ↓reduceIte]; omega) hζF
                (fun e => by cases e) hζ
          · rename_i hζX
            simp only [Option.some.injEq] at h
            subst h
            exact Or.inl ⟨ζ, rfl, fun h' => hζX (ltB_iff.mpr h')⟩
        · cases h
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte] at hn
      cases z with
      | zero => rw [kNd_f_zero] at h; cases h
      | M j => rw [kNd_f_M] at h; cases h
      | plus a b =>
        rw [kNd_f_plus] at h
        obtain ⟨ha, hb, -, -⟩ := hz.plus
        simp only [Tm.size] at hn
        rcases maxOpt_cases h with h' | h'
        · exact ih false a u (by simp only [Bool.false_eq_true, ↓reduceIte]; omega) ha
            (fun e => by cases e) h'
        · exact ih false b u (by simp only [Bool.false_eq_true, ↓reduceIte]; omega) hb
            (fun e => by cases e) h'
      | Om e =>
        rw [kNd_f_om] at h
        simp only [Tm.size] at hn
        exact ih false e u (by simp only [Bool.false_eq_true, ↓reduceIte]; omega) hz.om.1
          (fun e => by cases e) h
      | Xi j a =>
        rw [kNd_f_xi] at h
        split at h
        · rename_i hlt
          exact ih true (.Xi j a) u (by simp only [↓reduceIte]; omega) hz (fun _ => ltB_iff.mp hlt) h
        · simp only [Tm.size] at hn
          exact ih false a u (by simp only [Bool.false_eq_true, ↓reduceIte]; omega) hz.xi.2.1
            (fun e => by cases e) h
      | Psi p a =>
        rw [kNd_f_psi] at h
        split at h
        · rename_i hlt
          exact ih true (.Psi p a) u (by simp only [↓reduceIte]; omega) hz (fun _ => ltB_iff.mp hlt) h
        · simp only [Tm.size] at hn
          rcases maxOpt_cases h with h' | h'
          · exact ih false p u (by simp only [Bool.false_eq_true, ↓reduceIte]; omega) hz.psi.piF
              (fun e => by cases e) h'
          · exact ih false a u (by simp only [Bool.false_eq_true, ↓reduceIte]; omega) hz.psi.aF
              (fun e => by cases e) h'

/-- 塔の始点（`0` でない）は障害の形で、`Ξ_m(pre ⊕ R[0])` 以上 -/
theorem kTop_form {τ : Tm} {m : Nat} {pre : List Tm} {R : Tm} {r : SeqD} (hm : 1 ≤ m) (hτ : WNF τ)
    (hτM : Lt τ (.M m)) (hX : WNF (oadd (ofSummands pre) R)) (h0 : kTop τ m pre R r ≠ .zero) :
    KForm m (oadd (ofSummands pre) R) (kTop τ m pre R r) ∧
      ¬ Lt (kTop τ m pre R r) (.Xi m (oadd (ofSummands pre) (r.big .zero))) := by
  have hMF := WNF.M' hm
  rcases kTop_cases τ m pre R r with ⟨-, e⟩ | ⟨s, hs, ⟨e, -⟩ | e⟩
  · exact absurd e h0
  · exact absurd e h0
  · have h1 : ¬ ltB s (.Xi m (oadd (ofSummands pre) (r.big .zero))) = true := by
      intro h1
      apply h0
      unfold kTop; rw [hs]; simp only [h1, ↓reduceIte]
    rw [e]
    obtain ⟨e', he', hf⟩ := kNeed_spec hs
    have he'F := hτ.of_mem_subs (fr_spec he').1
    exact ⟨kNd_form hm hX _ true e' s (Nat.le_refl _) he'F
      (fun _ => lt_transY he'F hτ hMF (fr_spec he').2 hτM) hf, fun h => h1 (ltB_iff.mpr h)⟩

/-! ### 共終数 `M_m` の項の前線 -/

theorem one_mem_fr_psiS {m : Nat} (hm : 1 ≤ m) {a : Tm} (h : WNF (.Psi (succM m) a)) :
    one ∈ fr (.M m) (.Psi (succM m) a) := by
  have hlt : ¬ Lt (.Psi (succM m) a) (.M m) := Lt.asymmY (WNF.M' hm) h (M_lt_psiS hm h)
  have h1M : Lt (Tm.Psi (.Om .zero) .zero) (.M m) := lt_of_lev_lt' (by show (1 : Nat) < m + 1; omega)
  simp only [fr, hlt, ↓reduceIte, List.mem_append]
  left
  simp [succM, fr, one, h1M]

/-- `M_m⁺` 未満（`M_m` 以上の節点の引数も `M_m⁺` 未満）で共終数が `M_m` の項の前線は、列の項に残る -/
theorem fr_sub_fsM {m : Nat} (hm : 1 ≤ m) : ∀ T : Tm, WNF T → Lt T (succM m) →
    inC T (succM m) (.M m) = true → dom T = .big (.M m) →
    ∀ ξ, WNF ξ → Lt ξ (.M m) → ∀ f, f ∈ fr (.M m) T → f ∈ fr (.M m) (fundBig T ξ) := by
  have hMF := WNF.M' hm
  have hSF := WNF.succM hm
  intro T
  induction T using size_induction with
  | h T ih =>
  intro hT hTS hTC hd ξ hξ hξM f hf
  have hB := (inv_of T hT).2 (.M m) hd
  have hMT : Le (.M m) T := hB.σle
  cases T with
  | zero => simp [fr] at hf
  | M n => simp [fr] at hf
  | plus a b =>
    obtain ⟨haF, hbF, hap, hb0⟩ := hT.plus
    have hbd : dom b = .big (.M m) := hd
    have hBb := (inv_of b hbF).2 (.M m) hbd
    have hxF := hBb.props.nf ξ hξ hξM
    have hxb := hBb.props.lt ξ hξ hξM
    rw [fundBig_plus]
    have hf' : f ∈ fr (.M m) a ∨ f ∈ fr (.M m) b := by simpa only [fr, List.mem_append] using hf
    rcases hf' with hfa | hfb
    · refine fr_of_mem_summands ?_ hfa
      cases hx : summands (fundBig b ξ) with
      | nil => rw [eq_zero_of_summands_nil hx, oadd_zero, summands_principal hap]; simp
      | cons h r =>
        rw [summands_oadd hx (nfl_principal (nfl_summands haF)) (nfl_principal (nfl_summands hxF)),
          summands_principal hap]
        obtain ⟨h', r', hb'⟩ := List.exists_cons_of_ne_nil (summands_ne_nil hb0)
        have e1 := head_le_of_lt hx hb' hxb
        have hhW := summands_WNF _ hxF h (by rw [hx]; exact List.mem_cons_self)
        have hh'W := summands_WNF _ hbF h' (by rw [hb']; exact List.mem_cons_self)
        have hha : Le h a := le_transY hhW.1 hh'W.1 haF
          (le_of_ne_gtY hhW.1 hh'W.1 (by rw [cmp_principal hhW.2 hh'W.2]; exact e1))
          (le_of_ne_gtY hh'W.1 haF (WNF.plus_head hT hb'))
        simp [le_leB hha]
    · have hbS := lt_transY hbF hT hSF (lt_plus_rightY hT) hTS
      have hbC : inC b (succM m) (.M m) = true := by
        rw [inC_plus, Bool.and_eq_true] at hTC; exact hTC.2
      exact fr_oadd_right haF hxF (ih b (by simp only [Tm.size]; omega) hbF hbS hbC hbd ξ hξ hξM f hfb)
  | Om e =>
    exfalso
    obtain ⟨heF, heOF⟩ := hT.om
    have heS : Lt e (.plus (.M m) one) := lt_om_iffG.mp hTS
    have heM : Lt e (.M m) := by
      rcases le_of_lt_succT heF hMF heS with h | h
      · rw [h] at heOF; cases heOF
      · exact h
    have hTM : Lt (.Om e) (.M m) := by
      rcases triY hT hMF with h | e' | h
      · exact h
      · cases e'
      · exact absurd ((lt_M_omY hm hT).mp h) (Lt.asymmY heF hMF heM)
    exact not_lt_of_leY hMF hT hMT hTM
  | Xi n a => rw [dom_xi] at hd; cases hd
  | Psi κ a =>
    rcases triY hT hMF with hTM | e | hMT'
    · exact absurd hTM (not_lt_of_leY hMF hT hMT)
    · cases e
    obtain ⟨Y, hY⟩ := prin_between_M hm hT rfl hMT' hTS
    obtain ⟨rfl, rfl⟩ := Tm.Psi.inj hY.symm
    have hnlt : ¬ Lt (.Psi (succM m) Y) (.M m) := Lt.asymmY hMF hT hMT'
    have hYF := hT.psi.aF
    have hTC' : inC Y (succM m) (.M m) = true ∧ Lt Y (succM m) := by
      rw [inC_psi] at hTC
      have h1 : (cmp (Tm.Psi (succM m) Y) (.M m) == .lt) = false := by
        rw [beq_eq_false_iff_ne]; exact hnlt
      rw [h1, Bool.false_or, Bool.and_eq_true, Bool.and_eq_true] at hTC
      exact ⟨hTC.1.2, beq_iff_eq.mp hTC.2⟩
    by_cases hY0 : Y = .zero
    · subst hY0
      have hcs : cs (succM m) .zero = .mul (.M m) 2 := by
        show cs (.Om (.plus (.M m) one)) .zero = _
        rw [cs_zero_om, ite_eq_right (by intro h; cases h)]
        rfl
      rw [dom_psi, hcs] at hd; cases hd
    by_cases hYs : isSucc Y = true
    · have hcs : cs (succM m) Y = .mul (.Psi (succM m) (pred Y)) 2 := cs_succ_om hYF hYs
      rw [dom_psi, hcs] at hd; cases hd
    obtain ⟨pa, Ra, hsa⟩ : ∃ pa Ra, summands Y = pa ++ [Ra] :=
      ⟨_, _, (List.dropLast_concat_getLast (summands_ne_nil hY0)).symm⟩
    have hNa : NFL (pa ++ [Ra]) := by rw [← hsa]; exact nfl_summands hYF
    have hRaW := hNa.1 Ra (by simp)
    have hRaF := hRaW.1
    have hRaq : Ra ∈ summands Y := by rw [hsa]; simp
    have hRaS : Lt Ra (succM m) :=
      lt_of_le_of_ltY hRaF hYF hSF (le_of_mem_summands hYF hRaq) hTC'.2
    have hcs := cs_succM_lim hYF hsa hYs hTC'.2 hm
    have hRd : dom Ra = .big (.M m) := by
      rw [dom_psi, hcs] at hd
      cases e : dom Ra with
      | big σ =>
        have hBR := (inv_of Ra hRaF).2 σ e
        have hσS : Lt σ (succM m) := lt_of_le_of_ltY hBR.props.σF hRaF hSF hBR.σle hRaS
        rw [app_psi00_big_dom e hσS] at hd
        exact hd
      | _ =>
        exfalso
        have e' : (info Ra).seq.dom = dom Ra := rfl
        simp only [SeqD.dom, e', e] at hd
        cases hd
    have hBRa := (inv_of Ra hRaF).2 (.M m) hRd
    have hxF := hBRa.props.nf ξ hξ hξM
    have hxR := hBRa.props.lt ξ hξ hξM
    have hTξ : fundBig (.Psi (succM m) Y) ξ = .Psi (succM m) (oadd (ofSummands pa) (fundBig Ra ξ)) := by
      rw [fundBig_psi, hcs]; exact app_psi00_big hxF
    have hWξ : WNF (.Psi (succM m) (oadd (ofSummands pa) (fundBig Ra ξ))) := by
      rw [← hTξ]; exact hB.props.nf ξ hξ hξM
    have hsum : summands (oadd (ofSummands pa) (fundBig Ra ξ)) = pa ++ summands (fundBig Ra ξ) :=
      summands_oadd_pre (pre := pa) hNa hxF hxR
    rw [hTξ]
    rcases fr_psiS hm hT f hf with e | hfY
    · rw [e]; exact one_mem_fr_psiS hm hWξ
    obtain ⟨u, hu, hfu⟩ := mem_fr_iff.mp hfY
    rw [hsa] at hu
    rcases List.mem_append.mp hu with hu | hu
    · exact fr_psiS_rev hm hWξ (fr_of_mem_summands (by rw [hsum]; exact List.mem_append_left _ hu) hfu)
    · rw [List.mem_singleton.mp hu] at hfu
      have hRaC : inC Ra (succM m) (.M m) = true := inC_of_mem_summands hYF hTC'.1 hRaq
      have hf' := ih Ra (by
        have := size_le_of_mem_subs (mem_subs_of_mem_summands hRaq)
        simp only [Tm.size]; omega) hRaF hRaS hRaC hRd ξ hξ hξM f hfu
      obtain ⟨v, hv, hfv⟩ := mem_fr_iff.mp hf'
      exact fr_psiS_rev hm hWξ (fr_of_mem_summands (by rw [hsum]; exact List.mem_append_right _ hv) hfv)


/-! ### `canonK` -/

theorem binv_psi_diag_K {π X R : Tm} {m : Nat} {pre : List Tm} (ht : WNF (.Psi π X))
    (hsX : summands X = pre ++ [R]) (hns : ¬ isSucc X = true)
    (hRd : dom R = .big (.M m)) (hRb : BInv R) (hMπ : ¬ Lt (.M m) π)
    (hold : kOld m pre R = false) : BInv (.Psi π X) := by
  have hP := ht.psi
  have hX := hP.aF
  have hπ := hP.piF
  have hπT := hP.tgt
  have hXn : NFL (pre ++ [R]) := by rw [← hsX]; exact nfl_summands hX
  have hPF := wnf_ofSummands (nfl_append_left hXn)
  have hR := hXn.1 R (by simp)
  have hR0 : R ≠ .zero := by intro e; rw [e] at hR; cases hR.2
  have hRX : R ∈ summands X := by rw [hsX]; simp
  have hRi := (inv_of R hR.1).2 (.M m) hRd
  have hRP := hRi.props
  have hMF : WNF (.M m) := hRP.σF
  have hm : 1 ≤ m := hMF.M
  have hSF := WNF.succM hm
  have hπM : Lt π (.M m) := by
    rcases triY hπ hMF with h | e | h
    · exact h
    · exact absurd e (hπT.notM m)
    · exact absurd h hMπ
  have htM : Lt (.Psi π X) (.M m) := lt_transY ht hπ hMF (lt_psi_targetY ht) hπM
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
  obtain ⟨c, hmk, hadj⟩ := mkApp_plain ht hsX hns (fundBig R (kTop π m pre R (info R).seq))
  have hcS := mkApp_shape hπ hmk
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
  obtain ⟨hG0F, hG0M, -⟩ := kTop_spec (pre := pre) (R := R) (r := (info R).seq) hm hπ hπM
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
  have hγSx : ∀ n, γ (n + 1) = .Xi m (xa pre .zero (fundBig R (γ n))) := fun n => by
    rw [hγS n, xa_zero pre (hxF _ (hγF n) (hγM n))]
  -- `Ξ_m(X)` と分割
  have hρX : WNF (.Xi m X) := WNF.mk_xi hm hX (ne_gt_of_le (Or.inr hXS)) hXCM
  have G : XG m X .zero pre [] R :=
    ⟨hρX, hsX, WNF.zero, zero_lt hR0, zero_lt (by intro e; cases e), Or.inl rfl⟩
  -- `X` の前線は `z₀ = Ξ_m(pre ⊕ R[0])` 未満
  have hz0F := hXiF .zero WNF.zero hRP.pos
  have hR0F := hxF .zero WNF.zero hRP.pos
  have hR0R := hRP.lt .zero WNF.zero hRP.pos
  have hRS : Lt R (succM m) := lt_of_le_of_ltY hR.1 hX hSF (le_of_mem_summands hX hRX) hXS
  have hRC : inC R (succM m) (.M m) = true :=
    inC_mono R X (.M m) (succM m) (.M m) (inC_of_mem_summands hX hXCM hRX) (fun _ _ h => h)
      (fun v hv hvX => lt_transY (hR.1.of_mem_subs hv) hX hSF hvX hXS)
  have hfrX : ∀ f, f ∈ fr (.M m) X → Lt f (.Xi m (oadd (ofSummands pre) (fundBig R .zero))) := by
    intro f hf
    have hsum0 := summands_oadd_pre (pre := pre) hXn hR0F hR0R
    obtain ⟨u, hu, hfu⟩ := mem_fr_iff.mp hf
    rw [hsX] at hu
    apply fr_lt_xi hz0F
    rcases List.mem_append.mp hu with hu | hu
    · exact fr_of_mem_summands (by rw [hsum0]; exact List.mem_append_left _ hu) hfu
    · rw [List.mem_singleton.mp hu] at hfu
      have h' := fr_sub_fsM hm R hR.1 hRS hRC hRd .zero WNF.zero hRP.pos f hfu
      obtain ⟨v, hv, hfv⟩ := mem_fr_iff.mp h'
      exact fr_of_mem_summands (by rw [hsum0]; exact List.mem_append_right _ hv) hfv
  -- 始点の段
  have hstart : Le (.Xi m (oadd (ofSummands pre) (fundBig R .zero))) (γ 1) ∧
      LBI (γ 0) (γ 1) ∧ (γ 0 = .zero ∨ (isPrincipal (γ 0) = true ∧ Lt (base (.M m)) (γ 0))) := by
    by_cases h0 : kTop π m pre R (info R).seq = .zero
    · have e0 : γ 0 = .zero := by rw [hγ0, h0]
      refine ⟨?_, by rw [e0]; exact lbi_zero _, Or.inl e0⟩
      rw [hγS 0, e0]; exact Or.inl rfl
    obtain ⟨hK, hz0s⟩ := kTop_form hm hπ hπM (by rw [← hXe]; exact hX) h0
    rw [← hγ0] at hK hz0s
    rw [← hXe] at hK
    have hsM := hγM 0
    have hs0 : γ 0 ≠ .zero := by rw [hγ0]; exact h0
    have hz0s' : Le (.Xi m (oadd (ofSummands pre) (fundBig R .zero))) (γ 0) :=
      le_of_not_ltY (hγF 0) hz0F hz0s
    have hB0F := hBF _ (hγF 0) hsM
    have hy1 : WNF (.Xi m (oadd (ofSummands pre) (fundBig R (γ 0)))) := by rw [← hγS 0]; exact hγF 1
    have hB0X := hBX _ (hγF 0) hsM
    have hx0 : fundBig R (γ 0) ≠ .zero := by
      intro e
      rcases hRi.ge (γ 0) (hγF 0) hsM with e' | h'
      · exact hs0 (e'.trans e)
      · rw [e] at h'; exact not_lt_zero _ h'
    have hC : ∀ d, WNF d → Lt (γ 0) d →
        inC (oadd (ofSummands pre) (fundBig R (γ 0))) (oadd (ofSummands pre) (fundBig R (γ 0))) d = true := by
      intro d hd hsd
      have hqD : inC X X d = true := inC_self_of_fr hXCM (fun f hf =>
        lt_of_lt_of_leY (fr_elem hX hf).1 hz0F hd (hfrX f hf)
          (Or.inr (lt_of_le_of_ltY hz0F (hγF 0) hd hz0s' hsd)))
      have hgap : ∀ v, v ∈ subs R → v ≠ R → Lt v R → Lt v (fundBig R (γ 0)) :=
        fun v hv hne hlt' => hRi.gapP hR.2 (γ 0) v (hγF 0) hsM hv hne hlt'
      have hpre := G.pre_inC (hxF _ (hγF 0) hsM) hgap (hRi.pos _ (hγF 0) hsM) hqD
      have hxC := hRi.ub _ _ (γ 0) (G.hAF (hxF _ (hγF 0) hsM)) (G.xa0 (hxF _ (hγF 0) hsM) hx0)
        (Cut.of_wnf hd) (hγF 0) hsM (inC_kTerm _ _ _) (hpre R (by simp))
        (inC_of_lt_cut (Cut.of_wnf hd) _ (hγF 0) hsd)
      have := G.inC_A (hxF _ (hγF 0) hsM) (fun s hs => hpre s (List.mem_append_left _ hs))
        (inC_zero _ _) hxC
      rwa [xa_zero pre (hxF _ (hγF 0) hsM)] at this
    have hprin : isPrincipal (γ 0) = true := by
      rcases hK with ⟨ζ, hζe, -⟩ | ⟨ζ, a, hζe, -⟩ <;> rw [hζe] <;> rfl
    refine ⟨Or.inr (lt_of_le_of_ltY hz0F (hγF 0) (hγF 1) hz0s' (hγm 0)), ?_,
      Or.inr ⟨hprin, lt_of_lt_of_leY (wnf_kTerm _) hz0F (hγF 0) (floorLev_lt_xi hz0F) hz0s'⟩⟩
    rw [hγS 0]
    rcases hK with ⟨ζ, hζe, hζX⟩ | ⟨ζ, a, hζe, hζX⟩
    · have hζW : WNF (.Xi m ζ) := by rw [← hζe]; exact hγF 0
      have hBζ : Lt (oadd (ofSummands pre) (fundBig R (γ 0))) ζ :=
        lt_of_lt_of_leY hB0F hX hζW.xi.2.1 hB0X (le_of_not_ltY hζW.xi.2.1 hX hζX)
      have h := lbi_xi_inv_hull hζW hy1 hBζ (fun d hd hζd => hC d hd (by rw [hζe]; exact hζd))
      rw [← hζe] at h
      exact h
    · have hsW : WNF (.Psi (.Xi m ζ) a) := by rw [← hζe]; exact hγF 0
      have hκ := hsW.psi.piF
      have hζF := hκ.xi.2.1
      have hBζ : Lt (oadd (ofSummands pre) (fundBig R (γ 0))) ζ :=
        lt_of_lt_of_leY hB0F hX hζF hB0X (le_of_not_ltY hζF hX hζX)
      have hBC : inC (oadd (ofSummands pre) (fundBig R (γ 0))) (oadd (ofSummands pre) (fundBig R (γ 0)))
          (.Xi m ζ) = true := hC _ hκ (by rw [hζe]; exact lt_psi_targetY hsW)
      have hBC' : inC (oadd (ofSummands pre) (fundBig R (γ 0))) ζ (.Xi m ζ) = true :=
        inC_mono _ _ _ _ _ hBC (fun _ _ h => h)
          (fun v hv hvB => lt_transY (hB0F.of_mem_subs hv) hB0F hζF hvB hBζ)
      have hlt' : Lt (.Xi m (oadd (ofSummands pre) (fundBig R (γ 0)))) (.Xi m ζ) :=
        (lt_xi_xi0 (Lt.ne hBζ)).mpr (Or.inl ⟨hBζ, hBC'⟩)
      have h := lbi_psi_seed_hull hsW hy1 hlt' (fun d hd hpd => hC d hd (by rw [hζe]; exact hpd))
      rw [← hζe] at h
      exact h
  obtain ⟨hz0γ1, hst, hadm0⟩ := hstart
  have hlad := lad_M G hRd hRi hRb hγSx hγF hγM hγm hadm0 hst
    (fun f hf => lt_of_lt_of_leY (fr_elem hX hf).1 hz0F (hγF 1) (hfrX f hf) hz0γ1)
  have hadm : ∀ n, γ n = .zero ∨ (isPrincipal (γ n) = true ∧ Lt (base (.M m)) (γ n)) := by
    intro n
    cases n with
    | zero => exact hadm0
    | succ n =>
      right
      have hyF := hγF (n + 1)
      rw [hγS n] at hyF ⊢
      exact ⟨rfl, floorLev_lt_xi hyF⟩
  have hRL : ∀ n, LBI (fundBig R (γ n)) (fundBig R (γ (n + 1))) := fun n =>
    hRb.big (.M m) hRd (γ n) (γ (n + 1)) (hγF n) (hγF _) (Or.inr (hγm n)) (hγM _) (hadm n) (hlad n)
  have hf : ∀ n, fundNat (.Psi π X) n = .Psi π (apx pre c (fundBig R (γ n))) := fun n => by
    rw [hfN n, combine_psi_zero pre hadj.cF (hxF _ (hγF n) (hγM n))]
  have htP := (props_all _ ht).1 hdom
  refine ⟨fun _ n => ?_, fun σ hd => by rw [hdom] at hd; cases hd⟩
  have hA := htP.nf n
  have hA' := htP.nf (n + 1)
  rw [hf] at hA hA' ⊢
  rw [hf]
  exact lbi_psi_apx ht hsX hadj.cF hadj.cR hcS (hxF _ (hγF n) (hγM n)) (hxF _ (hγF _) (hγM _))
    (Or.inr (hRP.mono _ _ (hγF n) (hγF _) (hγm n) (hγM _))) (hRP.lt _ (hγF _) (hγM _)) (hRL n) hA hA'

/-! ### まとめ -/

/-- `M_m` への対角化の梯子 -/
theorem psiDiagMBInv : PsiDiagMBInv := by
  intro π X R m pre ht hsX hns hRd hRb hMπ _
  cases hold : kOld m pre R with
  | true => exact binv_psi_diag_KO ht hsX hns hRd hRb hMπ hold
  | false => exact binv_psi_diag_K ht hsX hns hRd hRb hMπ hold

end MahloOCF.FS
