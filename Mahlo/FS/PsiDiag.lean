import Mahlo.FS.PsiXi

/-! 対角化：極限 `X = pre + R` の崩壊 `t = Ψ_π(X)` で、`R` の共終数 `σ` が `π` 以上の場合。

列は添字の列 `γ` による近似 `t[n] = Ψ_π(A_n)`、`A_n = pre ⊕ (c ⊕ R[γ_n])`（`natInv_psi_idx`）。

* 標準形・減少・単調・上界・隙間は素の近似と同じ（`approx_core` など）。添字 `γ_n` と `σ` の始点が
  `C(A_n, Ψ_π(A_n))` に入ることだけが要る。
* 共終性：`x < t` の大きさの帰納法（`cof_nat`）。`x = Ψ_π(a)`（`a = pre ⊕ a'`、`a' < R`）では、`a'` の
  `σ` についての前線が閉じた点 `γ_m` 未満なら `a' < R[γ_m]`（`R` の閉じた点での共終性）。 -/

namespace MahloOCF.FS

open Tm

/-! ### 近似の標準形 -/

/-- 添字 `ξ` と `σ` の始点が `C(A, Ψ_π(A))` に入れば、近似 `Ψ_π(A)`（`A = pre ⊕ (c ⊕ R[ξ])`）は標準形 -/
theorem approx_nf {π X R σ c ξ : Tm} {pre : List Tm} (ht : WNF (.Psi π X))
    (hsX : summands X = pre ++ [R]) (hRi : BigInv R σ) (hadj : AdjOK π pre R (fundBig R .zero) c)
    (hξ : WNF ξ) (hξσ : Lt ξ σ)
    (hC : inC ξ (apx pre c (fundBig R ξ)) (.Psi π (apx pre c (fundBig R ξ))) = true)
    (hB : inC (base σ) (apx pre c (fundBig R ξ)) (.Psi π (apx pre c (fundBig R ξ))) = true) :
    WNF (.Psi π (apx pre c (fundBig R ξ))) := by
  have hP := ht.psi
  have hX := hP.aF
  have hπ := hP.piF
  have hT := hP.tgt
  have hXn : NFL (pre ++ [R]) := by rw [← hsX]; exact nfl_summands hX
  have hPF := wnf_ofSummands (nfl_append_left hXn)
  have hR := hXn.1 R (by simp)
  have hRX : R ∈ summands X := by rw [hsX]; simp
  have hRP := hRi.props
  have hxF := hRP.nf ξ hξ hξσ
  have hmono0 : Le (fundBig R .zero) (fundBig R ξ) := by
    by_cases h0 : ξ = .zero
    · rw [h0]; exact Or.inl rfl
    · exact Or.inr (hRP.mono .zero ξ WNF.zero hξ (zero_lt h0) hξσ)
  obtain ⟨hAF, -, -, h4, hsC⟩ := approx_core (π := π) ht hsX hadj.cF hadj.cR hxF
    (hRP.lt ξ hξ hξσ) (fun v hv hne hlt => hRi.gapP hR.2 ξ v hξ hξσ hv hne hlt) (hRi.pos ξ hξ hξσ)
  have hval := hadj.valid _ hxF hmono0
  refine approx_wnf ht hsX hadj.cF hxF hAF hsC hval (approx_cC ht hadj hxF hPF hAF hval h4) ?_
  by_cases hA0 : apx pre c (fundBig R ξ) = .zero
  · have hx0 := (oadd_eq_zero hadj.cF hxF (oadd_eq_zero hPF (wnf_oadd hadj.cF hxF) hA0).2).2
    rw [hx0]; exact inC_zero _ _
  · exact hRi.ub _ _ ξ hAF hA0 (cut_psi hπ hT hAF) hξ hξσ hB (hsC R hRX) hC

/-! ### 添字の列による近似の列 -/

/-- `x` が `Ψ_π(a)` の形かどうか（構成的な場合分け） -/
theorem psi_form_dec (π x : Tm) : (∃ a, x = .Psi π a) ∨ ¬ ∃ a, x = .Psi π a := by
  cases x with
  | Psi ρ a =>
    by_cases e : ρ = π
    · exact Or.inl ⟨a, by rw [e]⟩
    · exact Or.inr (fun ⟨b, h⟩ => e (by cases h; rfl))
  | _ => exact Or.inr (fun ⟨b, h⟩ => by cases h)

/-- 添字の列 `γ` による近似 `Ψ_π(pre ⊕ (c ⊕ R[γ_n]))` の列の不変量（2 点の上界で、`σ` の始点は
`C(g, d)` に入るか添字以下） -/
theorem natInv_psi_idx' {π X R σ c : Tm} {pre : List Tm} (ht : WNF (.Psi π X))
    (hsX : summands X = pre ++ [R]) (hRi : BigInv R σ)
    (hadj : AdjOK π pre R (fundBig R .zero) c)
    (γ : Nat → Tm) (hγF : ∀ n, WNF (γ n)) (hγσ : ∀ n, Lt (γ n) σ)
    (hγm : ∀ n, Lt (γ n) (γ (n + 1)))
    (hf : ∀ n, fundNat (.Psi π X) n = .Psi π (apx pre c (fundBig R (γ n))))
    (hC : ∀ n, inC (γ n) (apx pre c (fundBig R (γ n))) (.Psi π (apx pre c (fundBig R (γ n)))) = true)
    (hB : ∀ n, inC (base σ) (apx pre c (fundBig R (γ n)))
      (.Psi π (apx pre c (fundBig R (γ n)))) = true)
    (hub : ∀ g d, WNF g → g ≠ .zero → Cut d → inC (.Psi π X) g d = true → ¬ Lt (.Psi π X) d →
      inC (base σ) g d = true ∧ ∀ n, inC (γ n) g d = true)
    (hcof : ∀ a a' N, WNF (.Psi π a) → WNF a' → Lt a X → summands a = pre ++ summands a' →
      Lt a' R → (∀ w, w ∈ fr π a → Lt w (.Psi π (apx pre c (fundBig R (γ N))))) →
      ∃ m, Lt a' (fundBig R (γ m)))
    (hub2 : ∀ g d n, WNF g → g ≠ .zero → Cut d →
      inC (.Psi π (apx pre c (fundBig R (γ (n + 1))))) g d = true →
      ¬ Lt (.Psi π (apx pre c (fundBig R (γ (n + 1))))) d →
      (inC (base σ) g d = true ∨ Le (base σ) (γ n)) ∧ inC (γ n) g d = true) :
    NatInv (.Psi π X) := by
  have hP := ht.psi
  have hX := hP.aF
  have hπ := hP.piF
  have hT := hP.tgt
  have hXn : NFL (pre ++ [R]) := by rw [← hsX]; exact nfl_summands hX
  have hPF := wnf_ofSummands (nfl_append_left hXn)
  have hR := hXn.1 R (by simp)
  have hRP := hRi.props
  have hxF : ∀ n, WNF (fundBig R (γ n)) := fun n => hRP.nf _ (hγF n) (hγσ n)
  have core := fun (n : Nat) => approx_core (π := π) ht hsX hadj.cF hadj.cR (hxF n)
    (hRP.lt _ (hγF n) (hγσ n))
    (fun v hv hne hlt => hRi.gapP hR.2 (γ n) v (hγF n) (hγσ n) hv hne hlt)
    (hRi.pos (γ n) (hγF n) (hγσ n))
  have hA'F : ∀ n, WNF (oadd c (fundBig R (γ n))) := fun n => wnf_oadd hadj.cF (hxF n)
  have hyF : ∀ n, WNF (.Psi π (apx pre c (fundBig R (γ n)))) := fun n =>
    approx_nf ht hsX hRi hadj (hγF n) (hγσ n) (hC n) (hB n)
  have hAmono : ∀ n, Lt (apx pre c (fundBig R (γ n))) (apx pre c (fundBig R (γ (n + 1)))) :=
    fun n => oadd_lt_oadd hPF (hA'F n) (hA'F (n + 1))
      (oadd_lt_oadd hadj.cF (hxF n) (hxF (n + 1))
        (hRP.mono _ _ (hγF n) (hγF (n + 1)) (hγm n) (hγσ (n + 1))))
  have hymono : ∀ n, Lt (Tm.Psi π (apx pre c (fundBig R (γ n))))
      (.Psi π (apx pre c (fundBig R (γ (n + 1))))) := fun n => lt_psi_psi_same.mpr (hAmono n)
  have hyt : ∀ n, Lt (Tm.Psi π (apx pre c (fundBig R (γ n)))) (.Psi π X) := fun n =>
    lt_psi_psi_same.mpr (core n).2.1
  refine ⟨⟨fun n => ?_, fun n => ?_, fun n => ?_, fun x hx hxt => ?_⟩, fun n => ?_,
    fun g d n hg hg0 hd hC' => ?_, fun n v hv hne hvt => ?_, fun g d n hg hg0 hd hC' => ?_⟩
  rotate_right
  · rw [hf] at hC' ⊢
    by_cases hlt : Lt (.Psi π (apx pre c (fundBig R (γ (n + 1))))) d
    · exact inC_of_lt_cut hd g (hyF n) (hd _ _ (hyF n) (hyF (n + 1)) (hymono n) hlt)
    obtain ⟨hbC, hγC⟩ := hub2 g d n hg hg0 hd hC' hlt
    exact approx_ub2 ht hsX hadj (hxF n) (hxF (n + 1)) (hRP.lt _ (hγF (n + 1)) (hγσ (n + 1)))
      (hRP.mono _ _ (hγF n) (hγF (n + 1)) (hγm n) (hγσ (n + 1))) (hyF n) (hyF (n + 1)) hg hg0 hd hC'
      (hRi.ub2 g d (γ n) (γ (n + 1)) hg hg0 hd (hγF n) (hγF (n + 1)) (hγm n) (hγσ (n + 1)) hbC hγC)
  · rw [hf]; exact hyF n
  · rw [hf]; exact hyt n
  · rw [hf, hf]; exact hymono n
  · -- 共終性
    obtain ⟨n, hn⟩ := cof_nat (t := .Psi π X) hyF hymono (fun x hx hxt N hN => by
      rcases psi_form_dec π x with hxa | hxa
      · obtain ⟨a, rfl⟩ := hxa
        have haF := hx.psi.aF
        have haX : Lt a X := lt_psi_psi_same.mp hxt
        rcases lt_split hX hsX haF haX with hle | ⟨a', ha', -, ha'R, hsa, hae⟩
        · refine ⟨N + 1, lt_psi_psi_same.mpr (lt_of_le_of_ltY haF hPF (core (N + 1)).1 hle ?_)⟩
          exact lt_of_le_of_ltY hPF (core N).1 (core (N + 1)).1 (le_oadd_leftW hPF (hA'F N))
            (hAmono N)
        · have hfrN : ∀ w, w ∈ fr π a → Lt w (.Psi π (apx pre c (fundBig R (γ N)))) :=
            fun w hw => hN w (by simp [parL, hw]) (lt_transY (hx.of_mem_subs
              (subs_psi_a (fr_spec hw).1)) hx ht (k2Y hx w hw) hxt)
          obtain ⟨m, hm⟩ := hcof a a' N hx ha' haX hsa ha'R hfrN
          refine ⟨m, lt_psi_psi_same.mpr ?_⟩
          rw [hae]
          exact oadd_lt_oadd hPF ha' (hA'F m)
            (lt_of_lt_of_leY ha' (hxF m) (hA'F m) hm (le_oadd_right hadj.cF (hxF m)))
      · refine ⟨N, psi_step ht (hyF N) hx hxt (fun w hw => ?_) (fun ρ a e hρt => ?_)
          (fun a e => absurd ⟨a, e⟩ hxa)⟩
        · have hwF := hx.of_mem_subs (parF_mem_subs hw)
          exact hN w (parF_sub_parL hw) (lt_transY hwF hx ht (parF_lt hx hw) hxt)
        · subst e
          exact hN ρ (by simp [parL]) hρt) x hx hxt
    exact ⟨n, by rw [hf]; exact Or.inr hn⟩
  · rw [hf]; intro e; cases e
  · rw [hf]
    by_cases hlt : Lt (.Psi π X) d
    · exact inC_of_lt_cut hd g (hyF n) (hd _ _ (hyF n) ht (hyt n) hlt)
    · obtain ⟨hbC, hγC⟩ := hub g d hg hg0 hd hC' hlt
      exact approx_ub ht hsX hadj (hxF n) (hyF n) (core n).2.1 hg hg0 hd hC'
        (fun hRC => hRi.ub g d (γ n) hg hg0 hd (hγF n) (hγσ n) hbC hRC (hγC n))
  · rw [hf]
    exact approx_gap ht (core n).2.2.1 (core n).2.2.2.1 v hv hne hvt

/-- 添字の列 `γ` による近似 `Ψ_π(pre ⊕ (c ⊕ R[γ_n]))` の列の不変量 -/
theorem natInv_psi_idx {π X R σ c : Tm} {pre : List Tm} (ht : WNF (.Psi π X))
    (hsX : summands X = pre ++ [R]) (hRi : BigInv R σ)
    (hadj : AdjOK π pre R (fundBig R .zero) c)
    (γ : Nat → Tm) (hγF : ∀ n, WNF (γ n)) (hγσ : ∀ n, Lt (γ n) σ)
    (hγm : ∀ n, Lt (γ n) (γ (n + 1)))
    (hf : ∀ n, fundNat (.Psi π X) n = .Psi π (apx pre c (fundBig R (γ n))))
    (hC : ∀ n, inC (γ n) (apx pre c (fundBig R (γ n))) (.Psi π (apx pre c (fundBig R (γ n)))) = true)
    (hB : ∀ n, inC (base σ) (apx pre c (fundBig R (γ n)))
      (.Psi π (apx pre c (fundBig R (γ n)))) = true)
    (hub : ∀ g d, WNF g → g ≠ .zero → Cut d → inC (.Psi π X) g d = true → ¬ Lt (.Psi π X) d →
      inC (base σ) g d = true ∧ ∀ n, inC (γ n) g d = true)
    (hcof : ∀ a a' N, WNF (.Psi π a) → WNF a' → Lt a X → summands a = pre ++ summands a' →
      Lt a' R → (∀ w, w ∈ fr π a → Lt w (.Psi π (apx pre c (fundBig R (γ N))))) →
      ∃ m, Lt a' (fundBig R (γ m)))
    (hub2 : ∀ g d n, WNF g → g ≠ .zero → Cut d →
      inC (.Psi π (apx pre c (fundBig R (γ (n + 1))))) g d = true →
      ¬ Lt (.Psi π (apx pre c (fundBig R (γ (n + 1))))) d →
      inC (base σ) g d = true ∧ inC (γ n) g d = true) :
    NatInv (.Psi π X) :=
  natInv_psi_idx' ht hsX hRi hadj γ hγF hγσ hγm hf hC hB hub hcof
    (fun g d n hg hg0 hd hC' hlt => ⟨Or.inl (hub2 g d n hg hg0 hd hC' hlt).1,
      (hub2 g d n hg hg0 hd hC' hlt).2⟩)

/-! ### 列の記述の評価 -/

theorem _root_.MahloOCF.IsTgt.notM {π : Tm} (h : IsTgt π) : ∀ m, π ≠ .M m := by
  rcases h with rfl | ⟨c, rfl, -⟩ | ⟨n, p, rfl⟩ <;> intro m e <;> cases e

theorem canonK_notM {σ : Tm} (h : ∀ m, σ ≠ .M m) (g : Gen) (pre : List Tm) (R : Tm) :
    canonK σ g pre R = false := by
  cases σ with
  | M m => exact absurd rfl (h m)
  | _ => cases g <;> rfl

theorem outsideMode_self {π : Tm} (h : ∀ m, π ≠ .M m) (pre : List Tm) (R : Tm) :
    outsideMode π π (.psi π) pre R = false := by
  cases π with
  | M m => exact absurd rfl (h m)
  | _ => simp [outsideMode, Gen.tgt?]

theorem ltB_self (a : Tm) : ltB a a = false := by
  cases e : ltB a a with
  | false => rfl
  | true => exact absurd (ltB_iff.mp e) (Lt.irrefl _)

theorem gam_in_zero {π : Tm} (h : ∀ m, π ≠ .M m) (pre : List Tm) (R : Tm) (r : SeqD) (c : Tm) :
    gam π π (.psi π) pre R r c .zero 0 = .zero := by
  simp only [gam, canonK_notM h, outsideMode_self h, Bool.false_eq_true, ↓reduceIte]
  cases π <;> simp [seedOut]

theorem gam_in_succ {π : Tm} (h : ∀ m, π ≠ .M m) (pre : List Tm) (R : Tm) (r : SeqD) (c : Tm)
    (k : Nat) : gam π π (.psi π) pre R r c .zero (k + 1) =
      .Psi π (combine (.psi π) pre c .zero (r.big (gam π π (.psi π) pre R r c .zero k))) := by
  simp only [gam, canonK_notM h, outsideMode_self h, Bool.false_eq_true, ↓reduceIte, argOf,
    Gen.ap, ite_self]

theorem nat_app_in {π : Tm} (h : ∀ m, π ≠ .M m) (pre : List Tm) (R : Tm) (r : SeqD) (c : Tm)
    (hr : r.dom = .big π) (n : Nat) :
    (SeqD.app π (.psi π) pre R r .zero c).nat n =
      .Psi π (combine (.psi π) pre c .zero (r.big (gam π π (.psi π) pre R r c .zero n))) := by
  simp only [SeqD.nat, hr, ltB_self, Bool.false_eq_true, ↓reduceIte, argOf, canonK_notM h,
    outsideMode_self h, Gen.ap, ite_self]

/-! ### 目標そのものへの対角化（`σ = π`） -/

/-- `R ≠ M_m` 型なら `R[ξ] ≠ 0` -/
theorem fundBig_ne_zero {R σ ξ : Tm} (hRi : BigInv R σ) (hσM : ∀ m, σ ≠ .M m) (hξ : WNF ξ)
    (hξσ : Lt ξ σ) : fundBig R ξ ≠ .zero := by
  intro h0
  have hall := hRi.pos ξ hξ hξσ h0
  have hR0 : R ≠ .zero := by
    intro e
    have := hRi.σsub
    rw [e] at this
    simp only [subs, List.mem_singleton] at this
    rw [this] at hξσ
    exact not_lt_zero _ hξσ
  obtain ⟨m, rfl⟩ := eq_M_of_subs_self hR0 hall
  exact hσM m (hall σ hRi.σsub)

/-- 目標そのものへの対角化：`t[n] = Ψ_π(pre ⊕ (c ⊕ R[γ_n]))`、`γ_0 = 0`、`γ_{n+1} = t[n]` -/
theorem inv_psi_diag_in {π X R : Tm} {pre : List Tm} (ht : WNF (.Psi π X))
    (hsX : summands X = pre ++ [R]) (hns : ¬ isSucc X = true)
    (hRd : dom R = .big π) (hRi : BigInv R π) : Inv (.Psi π X) := by
  have hP := ht.psi
  have hX := hP.aF
  have hπ := hP.piF
  have hT := hP.tgt
  have hπM := hT.notM
  have hXn : NFL (pre ++ [R]) := by rw [← hsX]; exact nfl_summands hX
  have hPF := wnf_ofSummands (nfl_append_left hXn)
  have hRP := hRi.props
  have hr : (info R).seq.dom = .big π := hRd
  have hfirst : (info R).seq.first = fundBig R .zero := by unfold SeqD.first; rw [hr]; rfl
  have hk : kAdj π π (.psi π) pre R (info R).seq = .zero := by
    unfold kAdj
    rw [hr]
    cases π with
    | M m => exact absurd rfl (hπM m)
    | _ => simp [outsideMode_self hπM]
  obtain ⟨c, hmk, hadj⟩ := mkApp_plain ht hsX hns hk
    (by rw [hfirst]; exact hRP.nf .zero WNF.zero hRP.pos)
  rw [hfirst] at hadj
  have hcs : cs π X = .app π (.psi π) pre R (info R).seq zero c :=
    cs_lim_app hX hsX hns hmk (fun σ hd => by
      rw [hr] at hd; cases hd; exact Or.inr (Or.inl (outsideMode_self hπM _ _)))
  have hdom : dom (.Psi π X) = .omega := by
    rw [dom_psi, hcs]; simp only [SeqD.dom, hr, ltB_self, Bool.false_eq_true, ↓reduceIte]
  obtain ⟨γ, hγdef⟩ : ∃ γ : Nat → Tm, γ = gam π π (.psi π) pre R (info R).seq c .zero := ⟨_, rfl⟩
  have hγ0 : γ 0 = .zero := by rw [hγdef]; exact gam_in_zero hπM _ _ _ _
  have hγS : ∀ n, γ (n + 1) = .Psi π (combine (.psi π) pre c .zero (fundBig R (γ n))) := by
    intro n; rw [hγdef]; exact gam_in_succ hπM _ _ _ _ n
  have hfN : ∀ n, fundNat (.Psi π X) n = .Psi π (combine (.psi π) pre c .zero (fundBig R (γ n))) := by
    intro n; rw [fundNat_psi, hcs, hγdef]; exact nat_app_in hπM _ _ _ _ hr n
  -- 近似の引数が後者でないこと（`Ξ` への崩壊の始点の比較に使う）
  have hγns : ∀ n, π ≠ .Om .zero → ¬ isSucc (γ n) = true := by
    intro n hπ0
    cases n with
    | zero => rw [hγ0]; simp [isSucc, summands]
    | succ n =>
      rw [hγS n]
      intro he
      simp [isSucc, summands, one] at he
      exact hπ0 he.1
  -- `σ` の始点は近似の下
  have hbase : ∀ ξ, WNF ξ → Lt ξ π → ¬ isSucc ξ = true →
      Lt (base π) (.Psi π (apx pre c (fundBig R ξ))) := by
    intro ξ hξ hξπ hξns
    have hxF := hRP.nf ξ hξ hξπ
    have hx0 := fundBig_ne_zero hRi hπM hξ hξπ
    have hA'F := wnf_oadd hadj.cF hxF
    have hAF := wnf_oadd hPF hA'F
    have hA'0 : oadd c (fundBig R ξ) ≠ .zero := fun e => hx0 (oadd_eq_zero hadj.cF hxF e).2
    have hA0 : apx pre c (fundBig R ξ) ≠ .zero := fun e => hA'0 (oadd_eq_zero hPF hA'F e).2
    rcases hT with rfl | ⟨c', rfl, hs⟩ | ⟨m, d, rfl⟩
    · exact lt_psi_psi_same.mpr (zero_lt hA0)
    · exact lt_psi_psi_same.mpr (zero_lt hA0)
    · show Lt (.Psi (.Xi m d) (sc d)) _
      refine lt_psi_psi_same.mpr (succT_lt_of_not_succ hπ.xi.2.1 hAF ?_ ?_)
      · rw [isSucc_oadd hPF hA'F hA'0, isSucc_oadd hadj.cF hxF hx0]
        exact hRi.nsucc ξ hξ hξπ hξns (Or.inr (by intro e; cases e))
      · have hmono0 : Le (fundBig R .zero) (fundBig R ξ) := by
          by_cases h0 : ξ = .zero
          · rw [h0]; exact Or.inl rfl
          · exact Or.inr (hRP.mono .zero ξ WNF.zero hξ (zero_lt h0) hξπ)
        exact validR_iff.mp (hadj.valid _ hxF hmono0) d rfl
  have hbaseF := wnf_base hπ (IsRegY.tgt hT)
  -- 添字の列の性質
  have key : ∀ n, WNF (γ n) ∧ Lt (γ n) π ∧ ¬ isSucc (γ n) = true ∧
      Lt (γ n) (.Psi π (apx pre c (fundBig R (γ n)))) ∧
      WNF (.Psi π (apx pre c (fundBig R (γ n)))) := by
    have step : ∀ ξ, WNF ξ → Lt ξ π → ¬ isSucc ξ = true → Lt ξ (.Psi π (apx pre c (fundBig R ξ))) →
        WNF (.Psi π (apx pre c (fundBig R ξ))) := by
      intro ξ hξ hξπ hξns hξy
      have hAF := wnf_oadd hPF (wnf_oadd hadj.cF (hRP.nf ξ hξ hξπ))
      have hcut := cut_psi hπ hT hAF
      have hbl := hbase ξ hξ hξπ hξns
      exact approx_nf ht hsX hRi hadj hξ hξπ (inC_of_lt_cut hcut _ hξ hξy)
        (inC_of_lt_cut hcut _ hbaseF hbl)
    intro n
    induction n with
    | zero =>
      rw [hγ0]
      have h1 : ¬ isSucc Tm.zero = true := by simp [isSucc, summands]
      have h2 : Lt Tm.zero (.Psi π (apx pre c (fundBig R .zero))) := zero_lt (by intro e; cases e)
      exact ⟨WNF.zero, zero_lt hT.ne_zero, h1, h2, step _ WNF.zero (zero_lt hT.ne_zero) h1 h2⟩
    | succ n ih =>
      obtain ⟨hγF, hγπ, hγns', hγy, hyF⟩ := ih
      have hxF := hRP.nf _ hγF hγπ
      have e1 : γ (n + 1) = .Psi π (apx pre c (fundBig R (γ n))) := by
        rw [hγS n, combine_psi_zero pre hadj.cF hxF]
      have hns1 : ¬ isSucc (γ (n + 1)) = true := by
        rcases hT with rfl | ⟨c', rfl, hs⟩ | ⟨m, d, rfl⟩
        · rw [e1]
          intro he
          simp [isSucc, summands, one] at he
          have hA0 := he
          have hx0 := fundBig_ne_zero hRi hπM hγF hγπ
          exact hx0 (oadd_eq_zero hadj.cF hxF (oadd_eq_zero hPF (wnf_oadd hadj.cF hxF) hA0).2).2
        · exact hγns (n + 1) (by intro e; cases e; simp [isSucc, summands, one] at hs)
        · exact hγns (n + 1) (by intro e; cases e)
      have hπ1 : Lt (γ (n + 1)) π := by rw [e1]; exact lt_psi_targetY hyF
      have hlt : Lt (γ n) (γ (n + 1)) := by rw [e1]; exact hγy
      have hγF1 : WNF (γ (n + 1)) := by rw [e1]; exact hyF
      have hx1 := hRP.nf _ hγF1 hπ1
      have hm := hRP.mono _ _ hγF hγF1 hlt hπ1
      have hy1 : Lt (γ (n + 1)) (.Psi π (apx pre c (fundBig R (γ (n + 1))))) := by
        have h := lt_psi_psi_same (π := π).mpr (oadd_lt_oadd hPF (wnf_oadd hadj.cF hxF)
          (wnf_oadd hadj.cF hx1) (oadd_lt_oadd hadj.cF hxF hx1 hm))
        rw [← e1] at h
        exact h
      exact ⟨hγF1, hπ1, hns1, hy1, step _ hγF1 hπ1 hns1 hy1⟩
  have hγF : ∀ n, WNF (γ n) := fun n => (key n).1
  have hγπ : ∀ n, Lt (γ n) π := fun n => (key n).2.1
  have hyF : ∀ n, WNF (.Psi π (apx pre c (fundBig R (γ n)))) := fun n => (key n).2.2.2.2
  have hγS' : ∀ n, γ (n + 1) = .Psi π (apx pre c (fundBig R (γ n))) := fun n => by
    rw [hγS n, combine_psi_zero pre hadj.cF (hRP.nf _ (hγF n) (hγπ n))]
  have hf : ∀ n, fundNat (.Psi π X) n = .Psi π (apx pre c (fundBig R (γ n))) := fun n => by
    rw [hfN n, combine_psi_zero pre hadj.cF (hRP.nf _ (hγF n) (hγπ n))]
  have hcutA : ∀ n, Cut (.Psi π (apx pre c (fundBig R (γ n)))) := fun n =>
    cut_psi hπ hT (wnf_oadd hPF (wnf_oadd hadj.cF (hRP.nf _ (hγF n) (hγπ n))))
  refine ⟨fun _ => natInv_psi_idx ht hsX hRi hadj γ hγF hγπ
    (fun n => by rw [hγS' n]; exact (key n).2.2.2.1) hf
    (fun n => inC_of_lt_cut (hcutA n) _ (hγF n) (key n).2.2.2.1)
    (fun n => inC_of_lt_cut (hcutA n) _ hbaseF (hbase _ (hγF n) (hγπ n) (key n).2.2.1))
    (fun g d hg hg0 hd hC hlt => ?_) (fun a a' N hxF ha' haX hsa ha'R hfrN => ?_)
    (fun g d n hg hg0 hd hC hlt => ?_),
    fun σ hd => by rw [hdom] at hd; cases hd⟩
  · -- 上界
    rcases inC_psi_iff.mp hC with h1 | ⟨hπC, hXC, hXg⟩
    · exact absurd h1 hlt
    have hbC : inC (base π) g d = true := by
      have hπd : ¬ Lt π d := fun h' => hlt (hd _ _ ht hπ (lt_psi_targetY ht) h')
      rcases hT with rfl | ⟨c', rfl, hs⟩ | ⟨m, d', rfl⟩
      · exact inC_psi_iff.mpr (Or.inr ⟨hπC, inC_zero _ _, zero_lt hg0⟩)
      · exact inC_psi_iff.mpr (Or.inr ⟨hπC, inC_zero _ _, zero_lt hg0⟩)
      · rcases inC_xi_iff.mp hπC with h2 | ⟨hd'C, -⟩
        · exact absurd h2 hπd
        · have hd'F := hπ.xi.2.1
          have hd'X : Lt d' X := hP.act m d' rfl
          refine inC_psi_iff.mpr (Or.inr ⟨hπC, inC_succT (inC_one hg0) hd'C, ?_⟩)
          exact lt_of_le_of_ltY (succT_WNF hd'F) hX hg (succT_leY hd'F hX hd'X) hXg
    refine ⟨hbC, fun n => ?_⟩
    induction n with
    | zero => rw [hγ0]; exact inC_zero _ _
    | succ n ih =>
      rw [hγS' n]
      have hxF := hRP.nf _ (hγF n) (hγπ n)
      have core := approx_core (π := π) ht hsX hadj.cF hadj.cR hxF (hRP.lt _ (hγF n) (hγπ n))
        (fun v hv hne hlt => hRi.gapP (hXn.1 R (by simp)).2 (γ n) v (hγF n) (hγπ n) hv hne hlt)
        (hRi.pos (γ n) (hγF n) (hγπ n))
      exact approx_ub ht hsX hadj hxF (hyF n) core.2.1 hg hg0 hd hC
        (fun hRC => hRi.ub g d (γ n) hg hg0 hd (hγF n) (hγπ n) hbC hRC ih)
  · -- 共終性：`γ_{N+1} = t[N]` は閉じた点
    refine ⟨N + 1, hRi.clo ha' ha'R (hγF (N + 1)) (hγπ (N + 1)) ?_ ?_⟩
    · rw [hγS' N]; exact Cl.of_psi (hyF N)
    · intro f hf
      rw [hγS' N]
      exact hfrN f (fr_sub_of_summands (fun u hu => by rw [hsa]; exact List.mem_append_right _ hu) hf)
  · -- 2 点の上界
    have hA1F := (hyF (n + 1)).psi.aF
    rcases inC_psi_iff.mp hC with h1 | ⟨hπC, hAC, hAg⟩
    · exact absurd h1 hlt
    have hπd : ¬ Lt π d := fun h' => hlt (hd _ _ (hyF (n + 1)) hπ (lt_psi_targetY (hyF (n + 1))) h')
    have hbC : inC (base π) g d = true := by
      rcases hT with rfl | ⟨c', rfl, hs⟩ | ⟨m, d', rfl⟩
      · exact inC_psi_iff.mpr (Or.inr ⟨hπC, inC_zero _ _, zero_lt hg0⟩)
      · exact inC_psi_iff.mpr (Or.inr ⟨hπC, inC_zero _ _, zero_lt hg0⟩)
      · rcases inC_xi_iff.mp hπC with h2 | ⟨hd'C, -⟩
        · exact absurd h2 hπd
        · have hd'F := hπ.xi.2.1
          have hd'A : Lt d' (apx pre c (fundBig R (γ (n + 1)))) := (hyF (n + 1)).psi.act m d' rfl
          refine inC_psi_iff.mpr (Or.inr ⟨hπC, inC_succT (inC_one hg0) hd'C, ?_⟩)
          exact lt_of_le_of_ltY (succT_WNF hd'F) hA1F hg (succT_leY hd'F hA1F hd'A) hAg
    refine ⟨hbC, ?_⟩
    have hRp := (hXn.1 R (by simp)).2
    have hxC : ∀ k, inC (apx pre c (fundBig R (γ k))) g d = true → inC (γ k) g d = true := by
      intro k hk
      have hxkF := hRP.nf _ (hγF k) (hγπ k)
      have hcR : Lt (oadd c (fundBig R (γ k))) R :=
        oadd_lt_prin hadj.cF hxkF hRp hadj.cR (hRP.lt _ (hγF k) (hγπ k))
      obtain ⟨-, hyC⟩ := inC_oadd_pre hXn (wnf_oadd hadj.cF hxkF) hcR hk
      exact hRi.lo g d (γ k) hd (hγF k) (hγπ k) (inC_of_oadd_right hadj.cF hxkF hyC)
    have hγ1C := hxC (n + 1) hAC
    rw [hγS' n] at hγ1C
    by_cases hlt' : Lt (.Psi π (apx pre c (fundBig R (γ n)))) d
    · exact inC_of_lt_cut hd g (hγF n) (hd _ _ (hγF n) (hyF n) (key n).2.2.2.1 hlt')
    · rcases inC_psi_iff.mp hγ1C with h1 | ⟨-, hA0C, -⟩
      · exact absurd h1 hlt'
      · exact hxC n hA0C

end MahloOCF.FS
