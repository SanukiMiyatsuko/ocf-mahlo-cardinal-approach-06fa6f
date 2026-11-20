import Mahlo.FS.PsiDiag

/-! 対角化のうち外に足す型（`R` の共終数 `σ` が `M` でない崩壊先で `π < σ`）で、`Ψ_π(X) < Ψ_σ(X)` の場合。

* `T = Ψ_σ(X)` は標準形（`X ∈ C(X, t)` を `C(X, T)` に移せる）。
* 添字の塔 `γ_{k+1} = Ψ_σ(pre ⊕ (c_σ ⊕ R[γ_k]))`（`c_σ` は `σ` への崩壊の有効性の調整）は `T` の近似で、
  全て閉じた点。始点 `γ_0` は `pre ⊕ R[0]` が `σ` の下限を越えれば `0`、そうでなければ `Ψ_σ(pre ⊕ (c_σ ⊕ R[0]))`。
  `T` 未満の項は塔のどこかの下に入る（`cof_nat`・`coll_step`）。
* `x = Ψ_π(a) < t`（`a = pre ⊕ a'`）の `a'` の `σ` 未満の極大部分項は `C(X, T)` に入るので `T` 未満、
  したがって塔の下にあり、`a' < R[γ_m]`（`lclo`）。 -/

namespace MahloOCF.FS

open Tm

/-! ### 補題 -/

theorem zero_oadd {y : Tm} (hy : WNF y) : oadd .zero y = y := by
  unfold oadd
  cases hs : summands y with
  | nil => exact (eq_zero_of_summands_nil hs).symm
  | cons h r =>
    simp only [summands, List.takeWhile_nil, List.nil_append]
    rw [← hs]; exact ofSummands_summands y hy

theorem isTgt_of_reg_notM {σ : Tm} (h : IsRegY σ) (hM : ∀ m, σ ≠ .M m) : IsTgt σ := by
  rcases h with rfl | ⟨c, rfl, hs⟩ | ⟨n, rfl⟩ | ⟨n, p, rfl⟩
  · exact Or.inl rfl
  · exact Or.inr (Or.inl ⟨c, rfl, hs⟩)
  · exact absurd rfl (hM n)
  · exact Or.inr (Or.inr ⟨n, p, rfl⟩)

/-- `lfr` の元は、`σ` 以下の `d` について `C(g, d)` を受け継ぐ -/
theorem inC_lfr {σ g d : Tm} (hσ : WNF σ) (hd : WNF d) (hdσ : Le d σ) :
    ∀ {a f : Tm}, WNF a → inC a g d = true → f ∈ lfr σ a → inC f g d = true := by
  intro a
  induction a using size_induction with
  | h a ih =>
  intro f ha h hf
  by_cases haσ : Lt a σ
  · rw [lfr_of_lt haσ, List.mem_singleton] at hf; rw [hf]; exact h
  have had : ¬ Lt a d := fun h' => haσ (lt_of_lt_of_leY ha hd hσ h' hdσ)
  cases a with
  | zero | M _ => simp [lfr, haσ] at hf
  | plus a1 a2 =>
    obtain ⟨ha1, ha2, -, -⟩ := ha.plus
    rw [inC_plus, Bool.and_eq_true] at h
    rcases (mem_lfr_plus haσ).mp hf with hf | hf
    · exact ih a1 (by simp only [Tm.size]; omega) ha1 h.1 hf
    · exact ih a2 (by simp only [Tm.size]; omega) ha2 h.2 hf
  | Om e =>
    rw [inC_om] at h
    exact ih e (by simp only [Tm.size]; omega) ha.om.1 h ((mem_lfr_om haσ).mp hf)
  | Xi m e =>
    rcases inC_xi_iff.mp h with h1 | ⟨h1, -⟩
    · exact absurd h1 had
    · exact ih e (by simp only [Tm.size]; omega) ha.xi.2.1 h1 ((mem_lfr_xi haσ).mp hf)
  | Psi p e =>
    have hP := ha.psi
    rcases inC_psi_iff.mp h with h1 | ⟨h1, h2, -⟩
    · exact absurd h1 had
    · rcases (mem_lfr_psi haσ).mp hf with hf | hf
      · exact ih p (by simp only [Tm.size]; omega) hP.piF h1 hf
      · exact ih e (by simp only [Tm.size]; omega) hP.aF h2 hf

/-- `Ψ_ρ(b) < Ψ_σ(X)`（`ρ < σ`）なら `ρ < Ψ_σ(X)` -/
theorem tgt_lt_of_psi_lt {ρ b σ X : Tm} (hz : WNF (.Psi ρ b)) (hT : WNF (.Psi σ X)) (hρσ : Lt ρ σ)
    (h : Lt (.Psi ρ b) (.Psi σ X)) : Lt ρ (.Psi σ X) := by
  have hQ := hz.psi
  have hP := hT.psi
  have hρF := hQ.piF
  have hσF := hP.piF
  have hl1 : lev ρ ≤ lev σ := lev_le_of_lt_gen hρσ
  rcases Nat.lt_or_eq_of_le hl1 with hl | hl
  · exact lt_of_lev_lt' (by simp only [lev]; exact hl)
  rcases triY hρF hT with h1 | h1 | h1
  · exact h1
  · exfalso; rcases hQ.tgt with rfl | ⟨c, rfl, -⟩ | ⟨n, p, rfl⟩ <;> cases h1
  · exfalso
    have hne : ρ ≠ σ := fun e => Lt.ne hρσ e
    have hnlt := Lt.asymmY hρF hσF hρσ
    have hbase := (lt_psi_psi_ltT (β := b) (γ := X) hl hne hnlt).mp h
    rcases hQ.tgt with rfl | ⟨c, rfl, hs⟩ | ⟨n, p, rfl⟩
    · -- `ρ = Ω_0`：`Ψ_σ(X) < Ω_0` は起こらない
      rcases hP.tgt with rfl | ⟨c', rfl, hs'⟩ | ⟨n', p', rfl⟩
      · exact Lt.irrefl _ hρσ
      · have := (lt_psiOm_omY hT WNF.zero).mp h1
        rcases this with e | e
        · rw [e] at hs'; simp [isSucc, summands] at hs'
        · exact not_lt_zero _ e
      · have hOF : IsOF (Tm.Psi (.Xi n' p') X) := Or.inr ⟨n', p', X, rfl⟩
        exact not_lt_zero _ ((lt_OF_omY hOF hT WNF.zero).mp h1)
    · -- `ρ = Ω_c`
      have hcF := hρF.om.1
      have hb := (baseOf_om_succ hs).mp hbase
      rcases hP.tgt with rfl | ⟨c', rfl, hs'⟩ | ⟨n', p', rfl⟩
      · exact not_lt_zero _ (lt_om_iffG.mp hρσ)
      · have h2 : Le c' c := (lt_psiOm_omY hT hcF).mp h1
        exact not_lt_of_leY hσF.om.1 hcF h2 (lt_om_iffG.mp hρσ)
      · have hOF : IsOF (Tm.Psi (.Xi n' p') X) := Or.inr ⟨n', p', X, rfl⟩
        have h2 : Lt (Tm.Psi (.Xi n' p') X) c := (lt_OF_omY hOF hT hcF).mp h1
        have hpF := predT_WNF hcF hs
        have h3 : Le (Tm.Psi (.Xi n' p') X) (predT c) := le_pred_of_lt_succ hcF hs hT h2
        have h4 := le_transY hT hpF (wnf_omOf hpF) h3 (le_omOf hpF)
        exact not_lt_of_leY hT (wnf_omOf hpF) h4 hb
    · -- `ρ = Ξ_n(p)`
      have hl' : lev σ = n := by simpa [lev] using hl.symm
      rcases (lt_psi_xiY (π := σ) (a := X) (b := p) (n := n) hl').mp h1 with h2 | h2
      · apply h2
        rw [swapY hρF hσF]
        have : cmp (.Xi n p) σ = .lt := hρσ
        rw [this]; rfl
      · rw [h2] at hbase; cases hbase

/-- `Ψ_π(X) < Ψ_σ(X)` で `σ` が `X` の成分（`σ ≥ Ψ_π(X)`）なら `Ψ_σ(X)` は標準形 -/
theorem wnf_psi_up {π σ X : Tm} (ht : WNF (.Psi π X)) (hσF : WNF σ) (hσT : IsTgt σ)
    (hσC : inC σ X (.Psi π X) = true) (hσt : ¬ Lt σ (.Psi π X))
    (hT : Lt (.Psi π X) (.Psi σ X)) : WNF (.Psi σ X) := by
  have hP := ht.psi
  have hX := hP.aF
  refine WNF.mk_psi ⟨hσT, hσF, hX, fun m d e => ?_, ?_⟩
  · subst e
    rcases inC_xi_iff.mp hσC with h | ⟨-, h⟩
    · exact absurd h hσt
    · exact h
  · have hcut := cut_psi hσF hσT hX
    exact inC_mono X X _ X _ hP.Ca (fun v hv hvt => hcut v _ (hX.of_mem_subs hv) ht hvt hT)
      (fun _ _ h => h)

/-! ### 列の記述の評価 -/

theorem outsideMode_ne {π σ : Tm} (hM : ∀ m, σ ≠ .M m) (hne : σ ≠ π) (pre : List Tm) (R : Tm) :
    outsideMode π σ (.psi π) pre R = true := by
  cases σ with
  | M m => exact absurd rfl (hM m)
  | _ => simp [outsideMode, Gen.tgt?, hne]

theorem gam_out_zero {π σ : Tm} (hM : ∀ m, σ ≠ .M m) (hne : σ ≠ π) (pre : List Tm) (R : Tm)
    (r : SeqD) (c P : Tm) : gam π σ (.psi π) pre R r c P 0 =
      if validR σ (oadd (ofSummands pre) (r.big .zero)) then .zero
      else col σ (oadd (ofSummands pre) (oadd (adjOf σ pre) (r.big .zero))) 0 := by
  cases σ with
  | M m => exact absurd rfl (hM m)
  | _ => simp only [gam, canonK_notM hM, outsideMode_ne hM hne, Bool.false_eq_true, ↓reduceIte]

theorem gam_out_succ {π σ : Tm} (hM : ∀ m, σ ≠ .M m) (hne : σ ≠ π) (pre : List Tm) (R : Tm)
    (r : SeqD) (c P : Tm) (k : Nat) :
    gam π σ (.psi π) pre R r c P (k + 1) =
      col σ (oadd (ofSummands pre) (oadd (adjOf σ pre) (r.big (gam π σ (.psi π) pre R r c P k)))) k := by
  cases σ with
  | M m => exact absurd rfl (hM m)
  | _ => simp only [gam, canonK_notM hM, outsideMode_ne hM hne, Bool.false_eq_true, ↓reduceIte]

theorem col_notM {σ : Tm} (hM : ∀ m, σ ≠ .M m) (δ : Tm) (k : Nat) :
    col σ δ k = if validR σ δ then .Psi σ δ else base σ := by
  cases σ with
  | M m => exact absurd rfl (hM m)
  | _ => rfl

theorem nat_app_out {π σ : Tm} (hM : ∀ m, σ ≠ .M m) (hne : σ ≠ π) (pre : List Tm) (R : Tm)
    (r : SeqD) (c : Tm) (hr : r.dom = .big σ) (hσπ : ltB σ π = false) (n : Nat) :
    (SeqD.app π (.psi π) pre R r .zero c).nat n =
      .Psi π (combine (.psi π) pre c .zero (r.big (gam π σ (.psi π) pre R r c .zero n))) := by
  simp only [SeqD.nat, hr, hσπ, Bool.false_eq_true, ↓reduceIte, argOf, canonK_notM hM,
    outsideMode_ne hM hne, Gen.ap]

/-- `mkApp` の調整は `adjOf` -/
theorem mkApp_adjOf {π : Tm} {pre : List Tm} {R : Tm} {r : SeqD} {c : Tm}
    (h : mkApp π (.psi π) pre R r .zero .zero = some (.app π (.psi π) pre R r .zero c)) :
    c = adjOf π pre := by
  unfold mkApp at h
  unfold adjOf
  cases htr : tailRaw (argR? π) pre with
  | none =>
    simp only [ne_eq, not_true_eq_false, false_and, ↓reduceIte, Gen.tgt?, htr, Option.some.injEq,
      SeqD.app.injEq, true_and] at h
    exact h.symm
  | some rt =>
    simp only [ne_eq, not_true_eq_false, false_and, ↓reduceIte, Gen.tgt?, htr] at h
    split at h
    · cases h
    · simp only [Option.some.injEq, SeqD.app.injEq, true_and] at h
      exact h.symm

/-- 近似 `Ψ_π(pre ⊕ (c ⊕ R[ξ]))` の標準形（調整 `c` の条件を直接与える版） -/
theorem approx_nf' {π X R σ c ξ : Tm} {pre : List Tm} (ht : WNF (.Psi π X))
    (hsX : summands X = pre ++ [R]) (hRi : BigInv R σ) (hcF : WNF c) (hcR : Lt c R)
    (hξ : WNF ξ) (hξσ : Lt ξ σ)
    (hval : validR π (apx pre c (fundBig R ξ)) = true)
    (hcC : inC c (apx pre c (fundBig R ξ)) (.Psi π (apx pre c (fundBig R ξ))) = true)
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
  obtain ⟨hAF, -, -, -, hsC⟩ := approx_core (π := π) ht hsX hcF hcR hxF
    (hRP.lt ξ hξ hξσ) (fun v hv hne hlt => hRi.gapP hR.2 ξ v hξ hξσ hv hne hlt) (hRi.pos ξ hξ hξσ)
  refine approx_wnf ht hsX hcF hxF hAF hsC hval hcC ?_
  by_cases hA0 : apx pre c (fundBig R ξ) = .zero
  · have hx0 := (oadd_eq_zero hcF hxF (oadd_eq_zero hPF (wnf_oadd hcF hxF) hA0).2).2
    rw [hx0]; exact inC_zero _ _
  · exact hRi.ub _ _ ξ hAF hA0 (cut_psi hπ hT hAF) hξ hξσ hB (hsC R hRX) hC

/-! ### 外に足す型（`t < Ψ_σ(X)`） -/

/-- 外に足す型の塔の性質（Bachmann 性の証明で使う）：`t[n] = Ψ_π(pre ⊕ (c ⊕ R[γ_n]))`、
    `γ_{k+1} = Ψ_σ(pre ⊕ (c_σ ⊕ R[γ_k]))`、`γ_0` は `0` か `Ψ_σ(pre ⊕ (c_σ ⊕ R[0]))`、添字は `0` か `σ` の底より
    大きい主要項 -/
structure OutTower (π X R σ : Tm) (pre : List Tm) (c cσ : Tm) (γ : Nat → Tm) : Prop where
  hTF : WNF (.Psi σ X)
  hdom : dom (.Psi π X) = .omega
  hmk : mkApp π (.psi π) pre R (info R).seq .zero .zero =
    some (.app π (.psi π) pre R (info R).seq .zero c)
  adj : AdjOK π pre R (fundBig R .zero) c
  hmkσ : mkApp σ (.psi σ) pre R (info R).seq .zero .zero =
    some (.app σ (.psi σ) pre R (info R).seq .zero cσ)
  adjσ : AdjOK σ pre R .zero cσ
  f : ∀ n, fundNat (.Psi π X) n = .Psi π (apx pre c (fundBig R (γ n)))
  γF : ∀ n, WNF (γ n)
  γσ : ∀ n, Lt (γ n) σ
  γ0 : γ 0 = .zero ∨ γ 0 = .Psi σ (apx pre cσ (fundBig R .zero))
  hcol : ∀ n, γ (n + 1) = .Psi σ (apx pre cσ (fundBig R (γ n)))
  γm : ∀ n, Lt (γ n) (γ (n + 1))
  adm : ∀ n, γ n = .zero ∨ (isPrincipal (γ n) = true ∧ Lt (base σ) (γ n))

theorem inv_psi_diag_out_full {π X R σ : Tm} {pre : List Tm} (ht : WNF (.Psi π X))
    (hsX : summands X = pre ++ [R]) (hns : ¬ isSucc X = true)
    (hRd : dom R = .big σ) (hRi : BigInv R σ) (hπσ : Lt π σ) (hσM : ∀ m, σ ≠ .M m)
    (hT : Lt (.Psi π X) (.Psi σ X)) :
    Inv (.Psi π X) ∧ ∃ c cσ γ, OutTower π X R σ pre c cσ γ := by
  have hP := ht.psi
  have hX := hP.aF
  have hπ := hP.piF
  have hπT := hP.tgt
  have hXn : NFL (pre ++ [R]) := by rw [← hsX]; exact nfl_summands hX
  have hPF := wnf_ofSummands (nfl_append_left hXn)
  have hR := hXn.1 R (by simp)
  have hRX : R ∈ summands X := by rw [hsX]; simp
  have hRP := hRi.props
  have hσF := hRP.σF
  have hσT := isTgt_of_reg_notM hRi.σreg hσM
  have hσne : σ ≠ π := fun e => Lt.ne hπσ e.symm
  have hr : (info R).seq.dom = .big σ := hRd
  have hXe : X = oadd (ofSummands pre) R := eq_oadd_of_summands hX hsX
  have hRC : inC R X (.Psi π X) = true := inC_of_mem_summands hX hP.Ca hRX
  have hσC : inC σ X (.Psi π X) = true := hRi.σC X _ (Cut.of_wnf ht) hRC
  have hσt : Lt (.Psi π X) σ := lt_transY ht hπ hσF (lt_psi_targetY ht) hπσ
  have hTF : WNF (.Psi σ X) := wnf_psi_up ht hσF hσT hσC (Lt.asymmY ht hσF hσt) hT
  have hTσ : Lt (.Psi σ X) σ := lt_psi_targetY hTF
  have hσ0 : σ ≠ .Om .zero := by
    intro e; subst e
    exact not_lt_om_zero_of_reg hπ (IsRegY.tgt hπT) hπσ
  -- `σ` の始点 `base σ = Ψ_σ(b0)`
  have hbF := wnf_base hσF hRi.σreg
  have hbσ : Lt (base σ) σ := base_lt hσF hRi.σreg
  have hbPsi : ∃ b0, base σ = .Psi σ b0 := by
    rcases hσT with rfl | ⟨c', rfl, -⟩ | ⟨m, e, rfl⟩ <;> exact ⟨_, rfl⟩
  obtain ⟨b0, hb0e⟩ := hbPsi
  have hbCl : Cl σ (base σ) := by
    have h := hbF; rw [hb0e] at h ⊢; exact Cl.of_psi h
  have hb_ns : ¬ isSucc (base σ) = true := by
    rw [hb0e]; intro he; simp [isSucc, summands, one] at he; exact hσ0 he.1
  have hb_pos : Lt .zero (base σ) := by rw [hb0e]; exact zero_lt (by intro e; cases e)
  -- 列の記述
  have hfirst : (info R).seq.first = fundBig R .zero := by unfold SeqD.first; rw [hr]; rfl
  obtain ⟨c, hmk, hadj⟩ := mkApp_plain ht hsX hns ((info R).seq.first)
  rw [hfirst] at hadj
  have hTt : ltB (.Psi σ (oadd (ofSummands pre) R)) (.Psi π (oadd (ofSummands pre) R)) = false := by
    rw [← hXe]
    cases e : ltB (.Psi σ X) (.Psi π X) with
    | false => rfl
    | true => exact absurd (ltB_iff.mp e) (Lt.asymmY ht hTF hT)
  have hcs : cs π X = .app π (.psi π) pre R (info R).seq zero c :=
    cs_lim_app hX hsX hns hmk (fun σ' hd => by rw [hr] at hd; cases hd; exact Or.inr (Or.inr hTt))
  have hσπB : ltB σ π = false := by
    cases e : ltB σ π with
    | false => rfl
    | true => exact absurd (ltB_iff.mp e) (Lt.asymmY hπ hσF hπσ)
  have hdom : dom (.Psi π X) = .omega := by
    rw [dom_psi, hcs]; simp only [SeqD.dom, hr, hσπB, Bool.false_eq_true, ↓reduceIte]
  -- `σ` への崩壊の近似の調整 `c_σ`（`σ = Ξ_m(e)`、`e = pre ⊕ rt` なら `rt + 1`）
  obtain ⟨cσ, hmkσ, hadjσ⟩ := mkApp_plain (r := (info R).seq) hTF hsX hns .zero
  have hcσe : adjOf σ pre = cσ := (mkApp_adjOf hmkσ).symm
  have hcσF := hadjσ.cF
  -- 塔
  obtain ⟨γ, hγdef⟩ : ∃ γ : Nat → Tm, γ = gam π σ (.psi π) pre R (info R).seq c .zero := ⟨_, rfl⟩
  have hγ0 : γ 0 = if validR σ (oadd (ofSummands pre) (fundBig R .zero)) then .zero
      else col σ (apx pre cσ (fundBig R .zero)) 0 := by
    rw [hγdef, ← hcσe]; exact gam_out_zero hσM hσne _ _ _ _ _
  have hγS : ∀ n, γ (n + 1) = col σ (apx pre cσ (fundBig R (γ n))) n := by
    intro n; rw [hγdef, ← hcσe]; exact gam_out_succ hσM hσne _ _ _ _ _ n
  have hfN : ∀ n, fundNat (.Psi π X) n =
      .Psi π (combine (.psi π) pre c .zero (fundBig R (γ n))) := by
    intro n; rw [fundNat_psi, hcs, hγdef]; exact nat_app_out hσM hσne _ _ _ _ hr hσπB n
  -- `B ξ = pre ⊕ R[ξ]`
  have hxF : ∀ ξ, WNF ξ → Lt ξ σ → WNF (fundBig R ξ) := fun ξ hξ hξσ => hRP.nf ξ hξ hξσ
  have hx0 : ∀ ξ, WNF ξ → Lt ξ σ → fundBig R ξ ≠ .zero := fun ξ hξ hξσ =>
    fundBig_ne_zero hRi hσM hξ hξσ
  have hBF : ∀ ξ, WNF ξ → Lt ξ σ → WNF (oadd (ofSummands pre) (fundBig R ξ)) :=
    fun ξ hξ hξσ => wnf_oadd hPF (hxF ξ hξ hξσ)
  have hpreB : ∀ ξ, WNF ξ → Lt ξ σ → Lt (ofSummands pre) (oadd (ofSummands pre) (fundBig R ξ)) :=
    fun ξ hξ hξσ => lt_oadd_left hPF (hxF ξ hξ hξσ) (hx0 ξ hξ hξσ)
  -- `σ` への崩壊の近似 `A ξ = pre ⊕ (c_σ ⊕ R[ξ])`
  have hCσF : ∀ ξ, WNF ξ → Lt ξ σ → WNF (oadd cσ (fundBig R ξ)) := fun ξ hξ hξσ =>
    wnf_oadd hcσF (hxF ξ hξ hξσ)
  have hCσ0 : ∀ ξ, WNF ξ → Lt ξ σ → oadd cσ (fundBig R ξ) ≠ .zero := fun ξ hξ hξσ e =>
    hx0 ξ hξ hξσ (oadd_eq_zero hcσF (hxF ξ hξ hξσ) e).2
  have hCσR : ∀ ξ, WNF ξ → Lt ξ σ → Lt (oadd cσ (fundBig R ξ)) R := fun ξ hξ hξσ =>
    oadd_lt_prin hcσF (hxF ξ hξ hξσ) hR.2 hadjσ.cR (hRP.lt ξ hξ hξσ)
  have hAσF : ∀ ξ, WNF ξ → Lt ξ σ → WNF (apx pre cσ (fundBig R ξ)) := fun ξ hξ hξσ =>
    wnf_oadd hPF (hCσF ξ hξ hξσ)
  have hAσ0 : ∀ ξ, WNF ξ → Lt ξ σ → apx pre cσ (fundBig R ξ) ≠ .zero := fun ξ hξ hξσ e =>
    hCσ0 ξ hξ hξσ (oadd_eq_zero hPF (hCσF ξ hξ hξσ) e).2
  have hAσns : ∀ ξ, WNF ξ → Lt ξ σ → ¬ isSucc ξ = true →
      ¬ isSucc (apx pre cσ (fundBig R ξ)) = true := by
    intro ξ hξ hξσ hns'
    show ¬ isSucc (oadd (ofSummands pre) (oadd cσ (fundBig R ξ))) = true
    rw [isSucc_oadd hPF (hCσF ξ hξ hξσ) (hCσ0 ξ hξ hξσ),
      isSucc_oadd hcσF (hxF ξ hξ hξσ) (hx0 ξ hξ hξσ)]
    exact hRi.nsucc ξ hξ hξσ hns' (Or.inr hσ0)
  have hAσX : ∀ ξ, WNF ξ → Lt ξ σ → Lt (apx pre cσ (fundBig R ξ)) X := by
    intro ξ hξ hξσ
    have := oadd_lt_oadd hPF (hCσF ξ hξ hξσ) hR.1 (hCσR ξ hξ hξσ)
    rw [← hXe] at this; exact this
  have hBAσ : ∀ ξ, WNF ξ → Lt ξ σ →
      Le (oadd (ofSummands pre) (fundBig R ξ)) (apx pre cσ (fundBig R ξ)) := fun ξ hξ hξσ =>
    oadd_le_oadd hPF (hxF ξ hξ hξσ) (hCσF ξ hξ hξσ) (le_oadd_right hcσF (hxF ξ hξ hξσ))
  have hpreA : ∀ ξ, WNF ξ → Lt ξ σ → Lt (ofSummands pre) (apx pre cσ (fundBig R ξ)) :=
    fun ξ hξ hξσ => lt_of_lt_of_leY hPF (hBF ξ hξ hξσ) (hAσF ξ hξ hξσ) (hpreB ξ hξ hξσ) (hBAσ ξ hξ hξσ)
  have hvalσ : ∀ ξ, WNF ξ → Lt ξ σ → validR σ (apx pre cσ (fundBig R ξ)) = true := fun ξ hξ hξσ =>
    hadjσ.valid _ (hxF ξ hξ hξσ) (zero_le _)
  -- `σ = Ξ_m(e)` なら `e < X`
  have heX : ∀ e, argR? σ = some e → Lt e X := by
    intro e he
    obtain ⟨m, rfl⟩ := argR_some he
    rcases inC_xi_iff.mp hσC with h | ⟨-, h⟩
    · exact absurd h (Lt.asymmY ht hσF hσt)
    · exact h
  -- `ξ ≥ base σ` なら `e < pre ⊕ R[ξ]`
  have hvalid : ∀ ξ, WNF ξ → Lt ξ σ → Le (base σ) ξ → ∀ e, argR? σ = some e →
      Lt e (oadd (ofSummands pre) (fundBig R ξ)) := by
    intro ξ hξ hξσ hbξ e he
    have heX' := heX e he
    obtain ⟨m, rfl⟩ := argR_some he
    have heF := hσF.xi.2.1
    rcases lt_split hX hsX heF heX' with hle | ⟨e', he', he'0, he'R, hse, hee⟩
    · exact lt_of_le_of_ltY heF hPF (hBF ξ hξ hξσ) hle (hpreB ξ hξ hξσ)
    · rw [hee]
      have hξ0 : Lt .zero ξ := lt_of_lt_of_leY WNF.zero hbF hξ hb_pos hbξ
      refine oadd_lt_oadd hPF he' (hxF ξ hξ hξσ)
        (hRi.lclo e' ξ he' he'R hξ hξ0 hξσ (fun g hg => ?_))
      have hgF := he'.of_mem_subs (lfr_spec hg).1
      have hbF' : WNF (.Psi (.Xi m e) (sc e)) := hbF
      have heC : inC e (sc e) (.Psi (.Xi m e) (sc e)) = true := inC_of_succT hbF'.psi.Ca
      have he'C : inC e' (sc e) (.Psi (.Xi m e) (sc e)) = true := by
        rw [inC_iff_summandsW he']
        intro s hs
        exact inC_of_mem_summands heF heC (by rw [hse]; exact List.mem_append_right _ hs)
      have hgC := inC_lfr hσF hbF' (Or.inr (lt_psi_targetY hbF')) he' he'C hg
      exact lt_of_lt_of_leY hgF hbF' hξ (coll_psiY hbF' hgF hgC (lfr_spec hg).2) hbξ
  -- `base σ < Ψ_σ(B)`
  have hbase_lt : ∀ B, WNF B → B ≠ .zero → ¬ isSucc B = true → (∀ e, argR? σ = some e → Lt e B) →
      Lt (base σ) (.Psi σ B) := by
    intro B hB hB0 hBs hv
    rcases hσT with rfl | ⟨c', rfl, -⟩ | ⟨m, e, rfl⟩
    · exact lt_psi_psi_same.mpr (zero_lt hB0)
    · exact lt_psi_psi_same.mpr (zero_lt hB0)
    · exact lt_psi_psi_same.mpr (succT_lt_of_not_succ hσF.xi.2.1 hB hBs (hv e rfl))
  -- 近似 `A ξ` の `c_σ ⊕ R[ξ]` は、`Ψ_σ(A ξ)` を添字とする `R` の項の下
  have hAnext : ∀ ξ, WNF ξ → Lt ξ σ → WNF (.Psi σ (apx pre cσ (fundBig R ξ))) →
      Lt (oadd cσ (fundBig R ξ)) (fundBig R (.Psi σ (apx pre cσ (fundBig R ξ)))) := by
    intro ξ hξ hξσ hyF
    have hyσ : Lt (.Psi σ (apx pre cσ (fundBig R ξ))) σ := lt_psi_targetY hyF
    obtain ⟨-, hyC⟩ := inC_oadd_pre hXn (hCσF ξ hξ hξσ) (hCσR ξ hξ hξσ) hyF.psi.Ca
    refine hRi.lclo _ _ (hCσF ξ hξ hξσ) (hCσR ξ hξ hξσ) hyF (zero_lt (by intro e; cases e)) hyσ
      (fun f hf => ?_)
    have hfF := (hCσF ξ hξ hξσ).of_mem_subs (lfr_spec hf).1
    exact coll_psiY hyF hfF (inC_lfr hσF hyF (Or.inr hyσ) (hCσF ξ hξ hξσ) hyC hf) (lfr_spec hf).2
  -- `Ψ_σ(A ξ)` は標準形
  have hstepNF : ∀ ξ, WNF ξ → Lt ξ σ → ¬ isSucc ξ = true →
      Lt ξ (.Psi σ (apx pre cσ (fundBig R ξ))) → WNF (.Psi σ (apx pre cσ (fundBig R ξ))) := by
    intro ξ hξ hξσ hξns hξy
    have hval := hvalσ ξ hξ hξσ
    have hbl := hbase_lt _ (hAσF ξ hξ hξσ) (hAσ0 ξ hξ hξσ) (hAσns ξ hξ hξσ hξns) (validR_iff.mp hval)
    have hAF := hAσF ξ hξ hξσ
    have hcutY := cut_psi hσF hσT hAF
    obtain ⟨-, -, -, -, hsC⟩ := approx_core (π := σ) hTF hsX hcσF hadjσ.cR (hxF ξ hξ hξσ)
      (hRP.lt ξ hξ hξσ) (fun v hv hne hlt => hRi.gapP hR.2 ξ v hξ hξσ hv hne hlt) (hRi.pos ξ hξ hξσ)
    have hσCA : inC σ (apx pre cσ (fundBig R ξ)) (.Psi σ (apx pre cσ (fundBig R ξ))) = true :=
      hRi.σC _ _ hcutY (hsC R hRX)
    have hcC := hadjσ.cC _ _ hAF (hAσ0 ξ hξ hξσ) hcutY hσCA
      (fun h => Lt.irrefl _ (below_lt_tgt hσF hσT σ hσF h))
    exact approx_nf' hTF hsX hRi hcσF hadjσ.cR hξ hξσ hval hcC (inC_of_lt_cut hcutY _ hξ hξy)
      (inC_of_lt_cut hcutY _ hbF hbl)
  -- 塔の一段
  have hstep : ∀ ξ, WNF ξ → Lt ξ σ → ¬ isSucc ξ = true → Lt ξ (.Psi σ (apx pre cσ (fundBig R ξ))) →
      WNF (.Psi σ (apx pre cσ (fundBig R ξ))) ∧ Lt (.Psi σ (apx pre cσ (fundBig R ξ))) σ ∧
      ¬ isSucc (.Psi σ (apx pre cσ (fundBig R ξ))) = true ∧
      Lt (base σ) (.Psi σ (apx pre cσ (fundBig R ξ))) ∧
      Lt (.Psi σ (apx pre cσ (fundBig R ξ)))
        (.Psi σ (apx pre cσ (fundBig R (.Psi σ (apx pre cσ (fundBig R ξ)))))) := by
    intro ξ hξ hξσ hξns hξy
    have hyF := hstepNF ξ hξ hξσ hξns hξy
    have hyσ := lt_psi_targetY hyF
    refine ⟨hyF, hyσ, ?_, hbase_lt _ (hAσF ξ hξ hξσ) (hAσ0 ξ hξ hξσ) (hAσns ξ hξ hξσ hξns)
      (validR_iff.mp (hvalσ ξ hξ hξσ)), ?_⟩
    · intro he; simp [isSucc, summands, one] at he; exact hσ0 he.1
    · exact lt_psi_psi_same.mpr (oadd_lt_oadd hPF (hCσF ξ hξ hξσ) (hCσF _ hyF hyσ)
        (oadd_lt_oadd hcσF (hxF ξ hξ hξσ) (hxF _ hyF hyσ) (hRP.mono _ _ hξ hyF hξy hyσ)))
  have e0 : ¬ validR σ (oadd (ofSummands pre) (fundBig R .zero)) = true →
      γ 0 = .Psi σ (apx pre cσ (fundBig R .zero)) := fun hv0 => by
    rw [hγ0, ite_eq_right hv0, col_notM hσM, ite_eq_left (hvalσ _ WNF.zero hRP.pos)]
  have key : ∀ n, WNF (γ n) ∧ Lt (γ n) σ ∧ ¬ isSucc (γ n) = true ∧
      validR σ (oadd (ofSummands pre) (fundBig R (γ n))) = true ∧
      Lt (γ n) (.Psi σ (apx pre cσ (fundBig R (γ n)))) ∧
      (γ n = .zero ∨ (Lt (base σ) (γ n) ∧ Cl σ (γ n) ∧ isPrincipal (γ n) = true)) := by
    intro n
    induction n with
    | zero =>
      by_cases hv0 : validR σ (oadd (ofSummands pre) (fundBig R .zero)) = true
      · rw [hγ0, ite_eq_left hv0]
        exact ⟨WNF.zero, hRP.pos, by simp [isSucc, summands], hv0, zero_lt (by intro e; cases e),
          Or.inl rfl⟩
      · obtain ⟨hyF, hyσ, hyns, hby, hyy⟩ := hstep _ WNF.zero hRP.pos (by simp [isSucc, summands])
          (zero_lt (by intro e; cases e))
        rw [e0 hv0]
        exact ⟨hyF, hyσ, hyns, validR_iff.mpr (hvalid _ hyF hyσ (Or.inr hby)), hyy,
          Or.inr ⟨hby, Cl.of_psi hyF, rfl⟩⟩
    | succ n ih =>
      obtain ⟨hγF, hγσ, hγns, -, hγy, -⟩ := ih
      have e1 : γ (n + 1) = .Psi σ (apx pre cσ (fundBig R (γ n))) := by
        rw [hγS n, col_notM hσM, ite_eq_left (hvalσ _ hγF hγσ)]
      obtain ⟨hyF, hyσ, hyns, hby, hyy⟩ := hstep _ hγF hγσ hγns hγy
      rw [e1]
      exact ⟨hyF, hyσ, hyns, validR_iff.mpr (hvalid _ hyF hyσ (Or.inr hby)), hyy,
        Or.inr ⟨hby, Cl.of_psi hyF, rfl⟩⟩
  have hγF : ∀ n, WNF (γ n) := fun n => (key n).1
  have hγσ : ∀ n, Lt (γ n) σ := fun n => (key n).2.1
  have hγns : ∀ n, ¬ isSucc (γ n) = true := fun n => (key n).2.2.1
  have hγv : ∀ n, validR σ (oadd (ofSummands pre) (fundBig R (γ n))) = true := fun n =>
    (key n).2.2.2.1
  have hcol : ∀ n, γ (n + 1) = .Psi σ (apx pre cσ (fundBig R (γ n))) := fun n => by
    rw [hγS n, col_notM hσM, ite_eq_left (hvalσ _ (hγF n) (hγσ n))]
  have hγm : ∀ n, Lt (γ n) (γ (n + 1)) := fun n => by rw [hcol n]; exact (key n).2.2.2.2.1
  have hγpos : ∀ n, Lt (base σ) (γ (n + 1)) ∧ Cl σ (γ (n + 1)) := by
    intro n
    rcases (key (n + 1)).2.2.2.2.2 with h | h
    · exfalso; rw [hcol n] at h; cases h
    · exact ⟨h.1, h.2.1⟩
  have hγb : ∀ n, Le (base σ) (γ (n + 1)) := fun n => Or.inr (hγpos n).1
  have hγCl : ∀ n, Cl σ (γ (n + 1)) := fun n => (hγpos n).2
  have hγ0' : ∀ n, Lt .zero (γ (n + 1)) := fun n =>
    lt_of_lt_of_leY WNF.zero hbF (hγF (n + 1)) hb_pos (hγb n)
  -- `T` 未満の項は塔のどこかの下
  have hull : ∀ z, WNF z → Lt z (.Psi σ X) → ∃ m, Lt z (γ m) := by
    refine cof_nat (t := .Psi σ X) hγF hγm (fun z hz hzT N hN => ⟨N + 1 + 1, ?_⟩)
    have hyF : WNF (γ (N + 1 + 1)) := hγF (N + 1 + 1)
    have hNle : Le (γ N) (γ (N + 1 + 1)) := seq_mono_le hγF hγm (by omega)
    have hN1 : Le (γ N) (γ (N + 1)) := Or.inr (hγm N)
    rw [hcol (N + 1)] at hyF hNle ⊢
    refine coll_step hyF hz (lt_transY hz hTF hσF hzT hTσ) (fun w hw => ?_) (fun ρ b e hρσ => ?_)
      (fun b e => ?_)
    · have hwF := hz.of_mem_subs (parF_mem_subs hw)
      have h1 := hN w (parF_sub_parL hw) (lt_transY hwF hz hTF (parF_lt hz hw) hzT)
      exact lt_of_lt_of_leY hwF (hγF N) hyF h1 hNle
    · subst e
      have h1 := hN ρ (by simp [parL]) (tgt_lt_of_psi_lt hz hTF hρσ hzT)
      exact lt_of_lt_of_leY hz.psi.piF (hγF N) hyF h1 hNle
    · subst e
      have hbF' := hz.psi.aF
      have hbX : Lt b X := lt_psi_psi_same.mp hzT
      rcases lt_split hX hsX hbF' hbX with hle | ⟨b', hb', hb'0, hb'R, hsb, hbe⟩
      · exact lt_of_le_of_ltY hbF' hPF (hAσF _ (hγF _) (hγσ _)) hle (hpreA _ (hγF _) (hγσ _))
      · rw [hbe]
        refine lt_of_lt_of_leY (wnf_oadd hPF hb') (hBF _ (hγF _) (hγσ _)) (hAσF _ (hγF _) (hγσ _))
          (oadd_lt_oadd hPF hb' (hxF _ (hγF _) (hγσ _))
            (hRi.lclo b' (γ (N + 1)) hb' hb'R (hγF _) (hγ0' N) (hγσ _) (fun g hg => ?_)))
          (hBAσ _ (hγF _) (hγσ _))
        have hgF := hb'.of_mem_subs (lfr_spec hg).1
        refine hγCl N g hgF (lfr_spec hg).2 (fun f hf => ?_)
        have hf1 : f ∈ fr σ b' := fr_of_lfr hb' hg hf
        have hf2 : f ∈ fr σ b :=
          fr_sub_of_summands (fun u hu => by rw [hsb]; exact List.mem_append_right _ hu) hf1
        have hfF := hbF'.of_mem_subs (fr_spec hf2).1
        exact lt_of_lt_of_leY hfF (hγF N) (hγF _)
          (hN f (by simp [parL, hf2]) (lt_transY hfF hz hTF (k2Y hz f hf2) hzT)) hN1
  -- `t` の近似
  have hf : ∀ n, fundNat (.Psi π X) n = .Psi π (apx pre c (fundBig R (γ n))) := fun n => by
    rw [hfN n, combine_psi_zero pre hadj.cF (hxF _ (hγF n) (hγσ n))]
  have hcore := fun (n : Nat) => approx_core (π := π) ht hsX hadj.cF hadj.cR (hxF _ (hγF n) (hγσ n))
    (hRP.lt _ (hγF n) (hγσ n))
    (fun v hv hne hlt => hRi.gapP hR.2 (γ n) v (hγF n) (hγσ n) hv hne hlt)
    (hRi.pos (γ n) (hγF n) (hγσ n))
  have hAF : ∀ n, WNF (apx pre c (fundBig R (γ n))) := fun n => (hcore n).1
  have hA'F : ∀ n, WNF (oadd c (fundBig R (γ n))) := fun n => wnf_oadd hadj.cF (hxF _ (hγF n) (hγσ n))
  have hA'0 : ∀ n, oadd c (fundBig R (γ n)) ≠ .zero := fun n e =>
    hx0 _ (hγF n) (hγσ n) (oadd_eq_zero hadj.cF (hxF _ (hγF n) (hγσ n)) e).2
  have hA0 : ∀ n, apx pre c (fundBig R (γ n)) ≠ .zero := fun n e =>
    hA'0 n (oadd_eq_zero hPF (hA'F n) e).2
  have hAns : ∀ n, ¬ isSucc (apx pre c (fundBig R (γ n))) = true := by
    intro n
    show ¬ isSucc (oadd (ofSummands pre) (oadd c (fundBig R (γ n)))) = true
    rw [isSucc_oadd hPF (hA'F n) (hA'0 n),
      isSucc_oadd hadj.cF (hxF _ (hγF n) (hγσ n)) (hx0 _ (hγF n) (hγσ n))]
    exact hRi.nsucc _ (hγF n) (hγσ n) (hγns n) (Or.inr hσ0)
  have hBA : ∀ n, Le (oadd (ofSummands pre) (fundBig R (γ n))) (apx pre c (fundBig R (γ n))) :=
    fun n => oadd_le_oadd hPF (hxF _ (hγF n) (hγσ n)) (hA'F n)
      (le_oadd_right hadj.cF (hxF _ (hγF n) (hγσ n)))
  have hAm : ∀ n, Lt (apx pre c (fundBig R (γ n))) (apx pre c (fundBig R (γ (n + 1)))) := fun n =>
    oadd_lt_oadd hPF (hA'F n) (hA'F (n + 1)) (oadd_lt_oadd hadj.cF (hxF _ (hγF n) (hγσ n))
      (hxF _ (hγF _) (hγσ _)) (hRP.mono _ _ (hγF n) (hγF _) (hγm n) (hγσ _)))
  have hcutA : ∀ n, Cut (.Psi π (apx pre c (fundBig R (γ n)))) := fun n => cut_psi hπ hπT (hAF n)
  have hσy : ∀ n, ¬ Lt σ (.Psi π (apx pre c (fundBig R (γ n)))) := fun n h' =>
    Lt.asymmY hπ hσF hπσ (below_lt_tgt hπ hπT σ hσF h')
  have hσCA : ∀ n, inC σ (apx pre c (fundBig R (γ n))) (.Psi π (apx pre c (fundBig R (γ n)))) = true :=
    fun n => hRi.σC _ _ (hcutA n) ((hcore n).2.2.2.2 R hRX)
  -- `σ` の始点が `C(g, d)` に入る条件
  have hbaseC : ∀ g d, g ≠ .zero → inC σ g d = true →
      (∀ e, argR? σ = some e → inC e g d = true ∧ Lt (sc e) g) → inC (base σ) g d = true := by
    intro g d hg0 hσCg he
    rcases hσT with rfl | ⟨c', rfl, -⟩ | ⟨m, e, rfl⟩
    · exact inC_psi_iff.mpr (Or.inr ⟨hσCg, inC_zero _ _, zero_lt hg0⟩)
    · exact inC_psi_iff.mpr (Or.inr ⟨hσCg, inC_zero _ _, zero_lt hg0⟩)
    · obtain ⟨heC, hsg⟩ := he e rfl
      exact inC_psi_iff.mpr (Or.inr ⟨hσCg, inC_succT (inC_one hg0) heC, hsg⟩)
  have hB : ∀ n, inC (base σ) (apx pre c (fundBig R (γ n)))
      (.Psi π (apx pre c (fundBig R (γ n)))) = true := by
    intro n
    refine hbaseC _ _ (hA0 n) (hσCA n) (fun e he => ?_)
    have heA : Lt e (apx pre c (fundBig R (γ n))) :=
      lt_of_lt_of_leY (wnf_argR hσF he) (hBF _ (hγF n) (hγσ n)) (hAF n)
        (validR_iff.mp (hγv n) e he) (hBA n)
    refine ⟨?_, succT_lt_of_not_succ (wnf_argR hσF he) (hAF n) (hAns n) heA⟩
    have hσCn := hσCA n
    have hσyn := hσy n
    obtain ⟨m, rfl⟩ := argR_some he
    rcases inC_xi_iff.mp hσCn with h | ⟨h, -⟩
    · exact absurd h hσyn
    · exact h
  -- `σ` への崩壊の近似の引数は、その値を添字とする `t` の近似の引数未満
  have hAσA : ∀ ξ n, WNF ξ → Lt ξ σ → γ n = .Psi σ (apx pre cσ (fundBig R ξ)) →
      Lt (apx pre cσ (fundBig R ξ)) (apx pre c (fundBig R (γ n))) := by
    intro ξ n hξ hξσ he
    have hyF : WNF (.Psi σ (apx pre cσ (fundBig R ξ))) := by rw [← he]; exact hγF n
    have h1 := hAnext ξ hξ hξσ hyF
    rw [← he] at h1
    exact oadd_lt_oadd hPF (hCσF ξ hξ hξσ) (hA'F n)
      (lt_of_lt_of_leY (hCσF ξ hξ hξσ) (hxF _ (hγF n) (hγσ n)) (hA'F n) h1
        (le_oadd_right hadj.cF (hxF _ (hγF n) (hγσ n))))
  -- `σ` への崩壊の近似の所属
  have hAσC : ∀ ξ n, WNF ξ → Lt ξ σ →
      inC ξ (apx pre c (fundBig R (γ n))) (.Psi π (apx pre c (fundBig R (γ n)))) = true →
      inC (apx pre cσ (fundBig R ξ)) (apx pre c (fundBig R (γ n)))
        (.Psi π (apx pre c (fundBig R (γ n)))) = true := by
    intro ξ n hξ hξσ hξC
    refine inC_oadd hPF (hCσF ξ hξ hξσ) ((inC_ofSummands pre).mpr (fun s hs =>
      (hcore n).2.2.2.2 s (by rw [hsX]; exact List.mem_append_left _ hs))) ?_
    refine inC_oadd hcσF (hxF ξ hξ hξσ) (hadjσ.cC _ _ (hAF n) (hA0 n) (hcutA n) (hσCA n) (hσy n)) ?_
    exact hRi.ub _ _ ξ (hAF n) (hA0 n) (hcutA n) hξ hξσ (hB n) ((hcore n).2.2.2.2 R hRX) hξC
  have hpsiC : ∀ ξ n, WNF ξ → Lt ξ σ → γ n = .Psi σ (apx pre cσ (fundBig R ξ)) →
      inC ξ (apx pre c (fundBig R (γ n))) (.Psi π (apx pre c (fundBig R (γ n)))) = true →
      inC (γ n) (apx pre c (fundBig R (γ n))) (.Psi π (apx pre c (fundBig R (γ n)))) = true := by
    intro ξ n hξ hξσ he hξC
    by_cases hlt : Lt (γ n) (.Psi π (apx pre c (fundBig R (γ n))))
    · exact inC_of_lt_cut (hcutA n) _ (hγF n) hlt
    · have h : inC (.Psi σ (apx pre cσ (fundBig R ξ))) (apx pre c (fundBig R (γ n)))
          (.Psi π (apx pre c (fundBig R (γ n)))) = true :=
        inC_psi_iff.mpr (Or.inr ⟨hσCA n, hAσC ξ n hξ hξσ hξC, hAσA ξ n hξ hξσ he⟩)
      rw [← he] at h
      exact h
  have hC : ∀ n, inC (γ n) (apx pre c (fundBig R (γ n)))
      (.Psi π (apx pre c (fundBig R (γ n)))) = true := by
    intro n
    induction n with
    | zero =>
      by_cases hv0 : validR σ (oadd (ofSummands pre) (fundBig R .zero)) = true
      · have h0 : γ 0 = .zero := by rw [hγ0, ite_eq_left hv0]
        rw [h0]; exact inC_zero _ _
      · exact hpsiC .zero 0 WNF.zero hRP.pos (e0 hv0) (inC_zero _ _)
    | succ n ih =>
      refine hpsiC (γ n) (n + 1) (hγF n) (hγσ n) (hcol n) ?_
      exact inC_mono _ _ _ _ _ ih
        (fun v hv hvy => below_mono hπ hπT (hAF _) (hAF n) (Or.inr (hAm n))
          ((hγF n).of_mem_subs hv) hvy)
        (fun v hv hvA => lt_transY ((hγF n).of_mem_subs hv) (hAF n) (hAF _) hvA (hAm n))
  -- 上界
  have hub : ∀ g d, WNF g → g ≠ .zero → Cut d → inC (.Psi π X) g d = true → ¬ Lt (.Psi π X) d →
      inC (base σ) g d = true ∧ ∀ n, inC (γ n) g d = true := by
    intro g d hg hg0 hd hCt hlt
    rcases inC_psi_iff.mp hCt with h1 | ⟨-, hXC, hXg⟩
    · exact absurd h1 hlt
    have hRCg : inC R g d = true := inC_of_mem_summands hX hXC hRX
    have hσCg : inC σ g d = true := hRi.σC g d hd hRCg
    have hσd : ¬ Lt σ d := fun h' => hlt (hd _ _ ht hσF hσt h')
    have hbC : inC (base σ) g d = true := by
      refine hbaseC g d hg0 hσCg (fun e he => ?_)
      have heX' := heX e he
      have heF := wnf_argR hσF he
      refine ⟨?_, lt_of_le_of_ltY (succT_WNF heF) hX hg (succT_leY heF hX heX') hXg⟩
      obtain ⟨m, rfl⟩ := argR_some he
      rcases inC_xi_iff.mp hσCg with h | ⟨h, -⟩
      · exact absurd h hσd
      · exact h
    have hcσC : inC cσ g d = true := hadjσ.cC g d hg hg0 hd hσCg hσd
    have hpsi : ∀ ξ, WNF ξ → Lt ξ σ → inC ξ g d = true →
        inC (.Psi σ (apx pre cσ (fundBig R ξ))) g d = true := by
      intro ξ hξ hξσ hξC
      by_cases hyd : Lt (.Psi σ (apx pre cσ (fundBig R ξ))) d
      · exact inC_of_lt_node (Or.inr ⟨_, _, rfl⟩) hyd
      · refine inC_psi_iff.mpr (Or.inr ⟨hσCg, ?_,
          lt_transY (hAσF ξ hξ hξσ) hX hg (hAσX ξ hξ hξσ) hXg⟩)
        refine inC_oadd hPF (hCσF ξ hξ hξσ) ((inC_ofSummands pre).mpr (fun s hs =>
          inC_of_mem_summands hX hXC (by rw [hsX]; exact List.mem_append_left _ hs))) ?_
        exact inC_oadd hcσF (hxF ξ hξ hξσ) hcσC (hRi.ub g d ξ hg hg0 hd hξ hξσ hbC hRCg hξC)
    refine ⟨hbC, fun n => ?_⟩
    induction n with
    | zero =>
      by_cases hv0 : validR σ (oadd (ofSummands pre) (fundBig R .zero)) = true
      · rw [hγ0, ite_eq_left hv0]; exact inC_zero _ _
      · rw [e0 hv0]; exact hpsi .zero WNF.zero hRP.pos (inC_zero _ _)
    | succ n ih =>
      rw [hcol n]
      exact hpsi (γ n) (hγF n) (hγσ n) ih
  -- 共終性
  have hcof : ∀ a a' N, WNF (.Psi π a) → WNF a' → Lt a X → summands a = pre ++ summands a' →
      Lt a' R → (∀ w, w ∈ fr π a → Lt w (.Psi π (apx pre c (fundBig R (γ N))))) →
      ∃ m, Lt a' (fundBig R (γ m)) := by
    intro a a' N hxF ha' haX hsa ha'R _
    have haF := hxF.psi.aF
    have hxt : Lt (.Psi π a) (.Psi π X) := lt_psi_psi_same.mpr haX
    have hxT : Lt (.Psi π a) (.Psi σ X) := lt_transY hxF ht hTF hxt hT
    have haC : inC a X (.Psi σ X) = true := inC_mono a a _ X _ hxF.psi.Ca
      (fun v hv hvx => lt_transY (haF.of_mem_subs hv) hxF hTF hvx hxT)
      (fun v hv hva => lt_transY (haF.of_mem_subs hv) haF hX hva haX)
    have ha'C : inC a' X (.Psi σ X) = true := by
      rw [inC_iff_summandsW ha']
      intro s hs
      exact inC_of_mem_summands haF haC (by rw [hsa]; exact List.mem_append_right _ hs)
    have hgT : ∀ g, g ∈ lfr σ a' → Lt g (.Psi σ X) := fun g hg =>
      coll_psiY hTF (ha'.of_mem_subs (lfr_spec hg).1)
        (inC_lfr hσF hTF (Or.inr hTσ) ha' ha'C hg) (lfr_spec hg).2
    obtain ⟨M, hM⟩ := exists_bound (P := fun _ => True) hγF hγm (lfr σ a')
      (fun g hg => ha'.of_mem_subs (lfr_spec hg).1)
      (fun g hg _ => hull g (ha'.of_mem_subs (lfr_spec hg).1) (hgT g hg))
    refine ⟨M + 1, hRi.lclo a' (γ (M + 1)) ha' ha'R (hγF _) (hγ0' M) (hγσ _) (fun g hg => ?_)⟩
    exact lt_transY (ha'.of_mem_subs (lfr_spec hg).1) (hγF M) (hγF _) (hM g hg trivial) (hγm M)
  -- 2 点の上界
  have hub2 : ∀ g d n, WNF g → g ≠ .zero → Cut d →
      inC (.Psi π (apx pre c (fundBig R (γ (n + 1))))) g d = true →
      ¬ Lt (.Psi π (apx pre c (fundBig R (γ (n + 1))))) d →
      inC (base σ) g d = true ∧ inC (γ n) g d = true := by
    intro g d n hg hg0 hd hCy hlt
    rcases inC_psi_iff.mp hCy with h1 | ⟨-, hAC, -⟩
    · exact absurd h1 hlt
    have hcR : Lt (oadd c (fundBig R (γ (n + 1)))) R :=
      oadd_lt_prin hadj.cF (hxF _ (hγF _) (hγσ _)) hR.2 hadj.cR (hRP.lt _ (hγF _) (hγσ _))
    obtain ⟨-, hyC⟩ := inC_oadd_pre hXn (hA'F (n + 1)) hcR hAC
    have hγ1C := hRi.lo g d (γ (n + 1)) hd (hγF _) (hγσ _)
      (inC_of_oadd_right hadj.cF (hxF _ (hγF _) (hγσ _)) hyC)
    by_cases hlt1 : Lt (γ (n + 1)) d
    · refine ⟨?_, inC_of_lt_cut hd g (hγF n) (hd _ _ (hγF n) (hγF _) (hγm n) hlt1)⟩
      rcases hγb n with e | h
      · rw [e]; exact inC_of_lt_cut hd g (hγF _) hlt1
      · exact inC_of_lt_cut hd g hbF (hd _ _ hbF (hγF _) h hlt1)
    · have hyF1 : WNF (.Psi σ (apx pre cσ (fundBig R (γ n)))) := by
        rw [← hcol n]; exact hγF _
      rw [hcol n] at hγ1C hlt1
      rcases inC_psi_iff.mp hγ1C with h1 | ⟨hσCg, hBC, hBg⟩
      · exact absurd h1 hlt1
      obtain ⟨-, hxnC⟩ := inC_oadd_pre hXn (hCσF _ (hγF n) (hγσ n)) (hCσR _ (hγF n) (hγσ n)) hBC
      have hxnC' := inC_of_oadd_right hcσF (hxF _ (hγF n) (hγσ n)) hxnC
      refine ⟨hbaseC g d hg0 hσCg (fun e he => ?_), hRi.lo g d (γ n) hd (hγF n) (hγσ n) hxnC'⟩
      have hσd : ¬ Lt σ d := fun h' => hlt1 (hd _ _ hyF1 hσF (lt_psi_targetY hyF1) h')
      have heF := wnf_argR hσF he
      have heB : Lt e (apx pre cσ (fundBig R (γ n))) := validR_iff.mp (hvalσ _ (hγF n) (hγσ n)) e he
      refine ⟨?_, lt_of_le_of_ltY (succT_WNF heF) (hAσF _ (hγF n) (hγσ n)) hg
        (succT_leY heF (hAσF _ (hγF n) (hγσ n)) heB) hBg⟩
      obtain ⟨m, rfl⟩ := argR_some he
      rcases inC_xi_iff.mp hσCg with h | ⟨h, -⟩
      · exact absurd h hσd
      · exact h
  refine ⟨⟨fun _ => natInv_psi_idx ht hsX hRi hadj γ hγF hγσ hγm hf hC hB hub hcof hub2,
    fun σ hd => by rw [hdom] at hd; cases hd⟩, c, cσ, γ,
    ⟨hTF, hdom, hmk, hadj, hmkσ, hadjσ, hf, hγF, hγσ, ?_, hcol, hγm, fun n => ?_⟩⟩
  · by_cases hv0 : validR σ (oadd (ofSummands pre) (fundBig R .zero)) = true
    · left; rw [hγ0, ite_eq_left hv0]
    · right; exact e0 hv0
  · rcases (key n).2.2.2.2.2 with h | h
    · exact Or.inl h
    · exact Or.inr ⟨h.2.2, h.1⟩

theorem inv_psi_diag_out {π X R σ : Tm} {pre : List Tm} (ht : WNF (.Psi π X))
    (hsX : summands X = pre ++ [R]) (hns : ¬ isSucc X = true)
    (hRd : dom R = .big σ) (hRi : BigInv R σ) (hπσ : Lt π σ) (hσM : ∀ m, σ ≠ .M m)
    (hT : Lt (.Psi π X) (.Psi σ X)) : Inv (.Psi π X) :=
  (inv_psi_diag_out_full ht hsX hns hRd hRi hπσ hσM hT).1

end MahloOCF.FS
