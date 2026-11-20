import Mahlo.FS.PsiK

/-! 仮想的な `M_m` への崩壊 `virtK m k = Ξ_m((ψ₀ ⊕ g_k) # Ξ_m(M_m⁺))`（`ψ₀ = Ψ_{M_m⁺}(0)`、
`g_{k+1} = Ψ_{M_m⁺}(ψ₀ ⊕ g_k)`）。`M_m` 未満の標準形は全てどれかの `virtK m n` 未満（`virt_all`）。

近似の引数が `M_m⁺` を越える `M_m` への対角化（`kOld`）の添字の塔に使う。 -/

namespace MahloOCF.FS

open Tm

/-! ### 自然な和の可換性 -/

theorem merge_comm : ∀ {A B : List Tm}, NFL A → NFL B → merge A B = merge B A
  | [], [], _, _ => rfl
  | [], b :: Bs, _, _ => by rw [merge.eq_1, merge.eq_2]
  | a :: As, [], _, _ => by rw [merge.eq_2, merge.eq_1]
  | a :: As, b :: Bs, hA, hB => by
    have haF := hA.1 a List.mem_cons_self
    have hbF := hB.1 b List.mem_cons_self
    rw [merge.eq_3, merge.eq_3]
    cases e : cmpP b a with
    | lt =>
      have h1 : leB b a = true := (leB_principal hbF.2 haF.2).mpr (by rw [e]; decide)
      have h2 : leB a b = false := by
        cases h : leB a b with
        | false => rfl
        | true =>
          rw [leB_principal haF.2 hbF.2, cmpP_swapP hbF haF, e] at h
          exact absurd rfl h
      rw [ite_eq_left h1, ite_eq_right (by rw [h2]; decide), merge_comm (nfl_tail hA) hB]
    | gt =>
      have h1 : leB b a = false := by
        cases h : leB b a with
        | false => rfl
        | true =>
          rw [leB_principal hbF.2 haF.2, e] at h
          exact absurd rfl h
      have h2 : leB a b = true := (leB_principal haF.2 hbF.2).mpr (by rw [cmpP_swapP hbF haF, e]; decide)
      rw [ite_eq_right (by rw [h1]; decide), ite_eq_left h2, merge_comm hA (nfl_tail hB)]
    | eq =>
      have hab := eq_of_cmpP_eqY hbF.1 haF.1 hbF.2 haF.2 e
      subst hab
      have h1 : leB b b = true := (leB_principal hbF.2 hbF.2).mpr (by rw [cmpP_self]; decide)
      rw [ite_eq_left h1, ite_eq_left h1]
      congr 1
      rw [merge_comm (nfl_tail hA) hB, merge_comm (nfl_tail hB) hA]
      cases As with
      | nil =>
        cases Bs with
        | nil => rfl
        | cons d Ds =>
          have hd : leB d b = true := (leB_iff).mpr hB.2.1
          rw [merge.eq_2, merge.eq_3, ite_eq_left hd, merge.eq_1]
      | cons c Cs =>
        have hc : leB c b = true := (leB_iff).mpr hA.2.1
        cases Bs with
        | nil => rw [merge.eq_3, ite_eq_left hc, merge.eq_2, merge.eq_1]
        | cons d Ds =>
          have hd : leB d b = true := (leB_iff).mpr hB.2.1
          rw [merge.eq_3 b (d :: Ds) c Cs, ite_eq_left hc, merge.eq_3 b (c :: Cs) d Ds, ite_eq_left hd,
            merge_comm (nfl_tail hB) (nfl_tail hA)]
termination_by A B => A.length + B.length

theorem nsum_comm {x y : Tm} (hx : WNF x) (hy : WNF y) : nsum x y = nsum y x := by
  unfold nsum
  rw [merge_comm (nfl_summands hx) (nfl_summands hy)]

theorem nsum_lt_left {x x' y : Tm} (hx : WNF x) (hx' : WNF x') (hy : WNF y) (h : Lt x x') :
    Lt (nsum x y) (nsum x' y) := by
  rw [nsum_comm hx hy, nsum_comm hx' hy]
  exact nsum_lt_right hy hx hx' h

theorem mem_merge_right : ∀ {l m : List Tm} {a : Tm}, a ∈ m → a ∈ merge l m
  | [], m, a, h => by rw [merge.eq_1]; exact h
  | x :: xs, [], a, h => by cases h
  | x :: xs, y :: ys, a, h => by
    rw [merge.eq_3]
    split
    · exact List.mem_cons_of_mem _ (mem_merge_right h)
    · rcases List.mem_cons.mp h with rfl | h
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (mem_merge_right h)
termination_by l m => l.length + m.length

/-- `y` の加数は `x # y` の加数 -/
theorem mem_summands_nsum_right {x y s : Tm} (hx : WNF x) (hy : WNF y) (hs : s ∈ summands y) :
    s ∈ summands (nsum x y) := by
  unfold nsum
  rw [summands_ofSummands _ (nfl_principal (nfl_merge (nfl_summands hx) (nfl_summands hy)))]
  exact mem_merge_right hs

/-! ### `M_m⁺` への崩壊の塔 `g_k` -/

section Virt

variable {m : Nat}

theorem succM_tgt (m : Nat) : IsTgt (succM m) := Or.inr (Or.inl ⟨_, rfl, rfl⟩)

theorem wnf_psi0M (hm : 1 ≤ m) : WNF (.Psi (succM m) .zero) :=
  wnf_base_om (WNF.succM hm) (Or.inr rfl)

theorem psi_lt_succM {a : Tm} : Lt (.Psi (succM m) a) (succM m) := lt_psiOm_om_self _ a

/-- `ψ₀ ⊕ g_k` -/
@[reducible] def virtE (m k : Nat) : Tm := oadd (.Psi (succM m) .zero) (virtG m k)

theorem virtG_succ (m k : Nat) : virtG m (k + 1) = .Psi (succM m) (virtE m k) := rfl

/-- 塔の各段は標準形で単調 -/
theorem virtG_spec (hm : 1 ≤ m) : ∀ k, WNF (virtG m (k + 1)) ∧ Lt (virtG m k) (virtG m (k + 1))
  | 0 => by
    have hψ := wnf_psi0M hm
    have hS := WNF.succM hm
    have e : virtE m 0 = .Psi (succM m) .zero := oadd_zero _
    have hy : WNF (.Psi (succM m) (virtE m 0)) := by
      rw [e]
      refine WNF.mk_psi ⟨succM_tgt m, hS, hψ, (fun n d e' => by cases e'), ?_⟩
      exact inC_of_lt_node (Or.inr ⟨_, _, rfl⟩) (lt_psi_psi_same.mpr (zero_lt (by intro e'; cases e')))
    exact ⟨hy, zero_lt (by intro e'; cases e')⟩
  | k + 1 => by
    obtain ⟨h1, h2⟩ := virtG_spec hm k
    have hψ := wnf_psi0M hm
    have hS := WNF.succM hm
    have hkF : WNF (virtG m k) := by
      cases k with
      | zero => exact WNF.zero
      | succ j => exact (virtG_spec hm j).1
    have hE : WNF (virtE m (k + 1)) := wnf_oadd hψ h1
    have hEm : Lt (virtE m k) (virtE m (k + 1)) := oadd_lt_oadd hψ hkF h1 h2
    have hE0 : virtE m (k + 1) ≠ .zero := fun e => by
      have := (oadd_eq_zero hψ h1 e).2
      rw [virtG_succ] at this
      cases this
    have hC : inC (virtE m (k + 1)) (virtE m (k + 1)) (.Psi (succM m) (virtE m (k + 1))) = true := by
      refine inC_oadd hψ h1 (inC_of_lt_node (Or.inr ⟨_, _, rfl⟩)
        (lt_psi_psi_same.mpr (zero_lt hE0))) ?_
      rw [virtG_succ]
      exact inC_of_lt_node (Or.inr ⟨_, _, rfl⟩) (lt_psi_psi_same.mpr hEm)
    have hy : WNF (.Psi (succM m) (virtE m (k + 1))) :=
      WNF.mk_psi ⟨succM_tgt m, hS, hE, (fun n d e' => by cases e'), hC⟩
    refine ⟨hy, ?_⟩
    rw [virtG_succ, virtG_succ]
    exact lt_psi_psi_same.mpr hEm

theorem virtG_F (hm : 1 ≤ m) : ∀ k, WNF (virtG m k)
  | 0 => WNF.zero
  | k + 1 => (virtG_spec hm k).1

theorem virtG_lt : ∀ k, Lt (virtG m k) (succM m)
  | 0 => zero_lt (by intro e; cases e)
  | _ + 1 => psi_lt_succM

theorem virtG_mono (hm : 1 ≤ m) (k : Nat) : Lt (virtG m k) (virtG m (k + 1)) := (virtG_spec hm k).2

theorem virtE_F (hm : 1 ≤ m) (k : Nat) : WNF (virtE m k) := wnf_oadd (wnf_psi0M hm) (virtG_F hm k)

theorem virtE_lt (hm : 1 ≤ m) (k : Nat) : Lt (virtE m k) (succM m) :=
  oadd_lt_prin (wnf_psi0M hm) (virtG_F hm k) rfl psi_lt_succM (virtG_lt k)

theorem virtE_mono (hm : 1 ≤ m) (k : Nat) : Lt (virtE m k) (virtE m (k + 1)) :=
  oadd_lt_oadd (wnf_psi0M hm) (virtG_F hm k) (virtG_F hm (k + 1)) (virtG_mono hm k)

theorem virtE_le_of (hm : 1 ≤ m) {j k : Nat} (h : j ≤ k) : Le (virtE m j) (virtE m k) :=
  seq_mono_le (virtE_F hm) (virtE_mono hm) h

theorem virtE_lt_of (hm : 1 ≤ m) {j k : Nat} (h : j < k) : Lt (virtE m j) (virtE m k) :=
  lt_of_lt_of_leY (virtE_F hm j) (virtE_F hm (j + 1)) (virtE_F hm k) (virtE_mono hm j)
    (virtE_le_of hm h)

theorem le_virtG_virtE (hm : 1 ≤ m) (k : Nat) : Le (virtG m k) (virtE m k) :=
  le_oadd_right (wnf_psi0M hm) (virtG_F hm k)

theorem M_lt_virtG1 (hm : 1 ≤ m) : Lt (.M m) (virtG m 1) :=
  coll_psiY (virtG_spec hm 0).1 (WNF.M' hm) (inC_M _ _ _) (M_lt_succM hm)

/-- `M_m⁺` 未満で、段 `g < M_m⁺`・切断 `M_m` で作れる項は塔 `g_k` の下 -/
theorem virtG_hull (hm : 1 ≤ m) {g : Tm} (hg : WNF g) (hgS : Lt g (succM m)) :
    ∀ z, WNF z → Lt z (succM m) → inC z g (.M m) = true → ∃ n, Lt z (virtG m (n + 1)) := by
  have hMF := WNF.M' hm
  have hSF := WNF.succM hm
  have hg1 := (virtG_spec hm 0).1
  have hMg1 := M_lt_virtG1 hm
  intro z
  induction z using size_induction with
  | h z ih =>
  intro hz hzS hzC
  by_cases hzM : Lt z (.M m)
  · exact ⟨0, lt_transY hz hMF hg1 hzM hMg1⟩
  cases z with
  | zero => exact absurd (zero_lt (by intro e; cases e)) hzM
  | M j =>
    exact ⟨0, bot_ltY rfl (show lev (Tm.M j) ≤ lev (succM m) from lev_le_of_lt_gen hzS) rfl rfl hg1⟩
  | plus a b =>
    obtain ⟨ha, -, -, -⟩ := hz.plus
    rw [inC_plus, Bool.and_eq_true] at hzC
    obtain ⟨n, hn⟩ := ih a (by simp only [Tm.size]; omega) ha
      (lt_transY ha hz hSF (lt_plus_leftY hz) hzS) hzC.1
    exact ⟨n, (lt_plus_prin_iffY hz rfl).mpr hn⟩
  | Om e =>
    have he : Lt e (.plus (.M m) one) := lt_om_iffG.mp hzS
    exact ⟨0, lt_om_psiOmG.mpr he⟩
  | Xi j b =>
    rcases Nat.lt_or_eq_of_le (show j ≤ lev (succM m) from lev_le_of_lt_gen hzS) with hl | hl
    · exact ⟨0, lt_of_lev_lt' hl⟩
    · exfalso
      have hOF : IsOF (.Xi j b) := Or.inl ⟨j, b, rfl⟩
      have h1 : Lt (.Xi j b) (.plus (.M m) one) := (lt_OF_omY hOF hz (succT_WNF hMF)).mp hzS
      have h2 : Le (.Xi j b) (.M m) := le_of_lt_succT hz hMF h1
      have h3 : Lt (.M m) (.Xi j b) := bot_ltY rfl
        (show m + 1 ≤ j by rw [hl]; exact Nat.le_max_right 1 (m + 1)) rfl rfl hz
      exact not_lt_of_leY hz hMF h2 h3
  | Psi ρ a =>
    have hP := hz.psi
    have hρF := hP.piF
    rcases inC_psi_iff.mp hzC with h | ⟨hρC, haC, hag⟩
    · exact absurd h hzM
    rcases triY hρF hSF with h1 | h1 | h1
    · obtain ⟨n, hn⟩ := ih ρ (by simp only [Tm.size]; omega) hρF h1 hρC
      exact ⟨n, lt_transY hz hρF (virtG_spec hm n).1 (lt_psi_targetY hz) hn⟩
    · subst h1
      have haF := hP.aF
      obtain ⟨n, hn⟩ := ih a (by simp only [Tm.size]; omega) haF (lt_transY haF hg hSF hag hgS) haC
      refine ⟨n + 1, ?_⟩
      rw [virtG_succ]
      exact lt_psi_psi_same.mpr (lt_of_lt_of_leY haF (virtG_F hm _) (virtE_F hm _) hn
        (le_virtG_virtE hm _))
    · have hl : lev ρ = lev (succM m) :=
        Nat.le_antisymm (show lev (Tm.Psi ρ a) ≤ lev (succM m) from lev_le_of_lt_gen hzS)
          (lev_le_of_lt_gen h1)
      have hne : ρ ≠ succM m := fun e => Lt.ne h1 e.symm
      have hb := not_base_of_lt_tgtY hz hSF (succM_tgt m) hl h1 hzS
      exact ⟨0, (lt_psi_psi_gtT (β := a) (γ := virtE m 0) hl hne h1).mpr hb⟩

/-! ### `virtK` -/

theorem wnf_xiS (hm : 1 ≤ m) : WNF (.Xi m (succM m)) := by
  refine WNF.mk_xi hm (WNF.succM hm) (by rw [cmp_self]; decide) ?_
  show inC (.Om (.plus (.M m) one)) _ _ = true
  rw [inC_om, inC_plus, inC_M, inC_one (by intro e; cases e)]
  rfl

theorem xiS_lt_M : Lt (.Xi m (succM m)) (.M m) := xi_lt_M _

/-- 仮想的な崩壊の引数 -/
@[reducible] def virtA (m k : Nat) : Tm := nsum (virtE m k) (.Xi m (succM m))

theorem virtK_eq (m k : Nat) : virtK m k = .Xi m (virtA m k) := rfl

theorem virtA_F (hm : 1 ≤ m) (k : Nat) : WNF (virtA m k) := wnf_nsum (virtE_F hm k) (wnf_xiS hm)

theorem virtA_lt (hm : 1 ≤ m) (k : Nat) : Lt (virtA m k) (succM m) :=
  nsum_lt_prin (virtE_F hm k) (wnf_xiS hm) rfl (virtE_lt hm k)
    (lt_transY (wnf_xiS hm) (WNF.M' hm) (WNF.succM hm) xiS_lt_M (M_lt_succM hm))

theorem virtE_le_A (hm : 1 ≤ m) (k : Nat) : Le (virtE m k) (virtA m k) :=
  le_nsum_left (virtE_F hm k) (wnf_xiS hm)

theorem virtA_mono (hm : 1 ≤ m) (k : Nat) : Lt (virtA m k) (virtA m (k + 1)) :=
  nsum_lt_left (virtE_F hm k) (virtE_F hm (k + 1)) (wnf_xiS hm) (virtE_mono hm k)

theorem virtA_le_of (hm : 1 ≤ m) {j k : Nat} (h : j ≤ k) : Le (virtA m j) (virtA m k) :=
  seq_mono_le (virtA_F hm) (virtA_mono hm) h

theorem virtA_ne_zero (hm : 1 ≤ m) (k : Nat) : virtA m k ≠ .zero := by
  intro e
  have h := le_nsum_right (virtE_F hm k) (wnf_xiS hm)
  rw [show nsum (virtE m k) (.Xi m (succM m)) = virtA m k from rfl, e] at h
  rcases h with h | h
  · cases h
  · exact not_lt_zero _ h

theorem inC_psi0M {g d : Tm} (h0 : Lt .zero g) : inC (.Psi (succM m) .zero) g d = true := by
  refine inC_psi_iff.mpr (Or.inr ⟨?_, inC_zero _ _, h0⟩)
  show inC (.Om (.plus (.M m) one)) g d = true
  rw [inC_om, inC_plus, inC_M, inC_one (by intro e; rw [e] at h0; exact not_lt_zero _ h0)]
  rfl

theorem inC_succM {g d : Tm} (hg0 : g ≠ .zero) : inC (succM m) g d = true := by
  show inC (.Om (.plus (.M m) one)) g d = true
  rw [inC_om, inC_plus, inC_M, inC_one hg0]
  rfl

theorem inC_virtG (hm : 1 ≤ m) {g d : Tm} (h0 : Lt .zero g) : ∀ k,
    (∀ j, j < k → Lt (virtE m j) g) → inC (virtG m k) g d = true
  | 0, _ => inC_zero _ _
  | k + 1, h => by
    have hg0 : g ≠ .zero := by intro e; rw [e] at h0; exact not_lt_zero _ h0
    rw [virtG_succ]
    exact inC_psi_iff.mpr (Or.inr ⟨inC_succM hg0,
      inC_oadd (wnf_psi0M hm) (virtG_F hm k) (inC_psi0M h0)
        (inC_virtG hm h0 k fun j hj => h j (by omega)), h k (by omega)⟩)

theorem inC_virtA (hm : 1 ≤ m) {g d : Tm} (h0 : Lt .zero g) (k : Nat)
    (h : ∀ j, j < k → Lt (virtE m j) g) (hx : inC (.Xi m (succM m)) g d = true) :
    inC (virtA m k) g d = true :=
  inC_nsum (virtE_F hm k) (wnf_xiS hm)
    (inC_oadd (wnf_psi0M hm) (virtG_F hm k) (inC_psi0M h0) (inC_virtG hm h0 k h)) hx

theorem wnf_virtK (hm : 1 ≤ m) (k : Nat) : WNF (virtK m k) := by
  rw [virtK_eq]
  have hAF := virtA_F hm k
  have hA0 : Lt .zero (virtA m k) := zero_lt (virtA_ne_zero hm k)
  refine WNF.mk_xi hm hAF (ne_gt_of_le (Or.inr (virtA_lt hm k))) ?_
  exact inC_virtA hm hA0 k (fun j hj => lt_of_lt_of_leY (virtE_F hm j) (virtE_F hm k) hAF
      (virtE_lt_of hm hj) (virtE_le_A hm k))
    (inC_of_lt_cut (Cut.of_wnf (WNF.M' hm)) _ (wnf_xiS hm) xiS_lt_M)

theorem virtK_lt_M (k : Nat) : Lt (virtK m k) (.M m) := xi_lt_M _

theorem xiS_lt_virtK (hm : 1 ≤ m) (k : Nat) : Lt (.Xi m (succM m)) (virtK m k) := by
  have hK := wnf_virtK hm k
  rw [virtK_eq] at hK ⊢
  refine k2xY hK _ ?_
  refine mem_fr_iff.mpr ⟨.Xi m (succM m),
    mem_summands_nsum_right (virtE_F hm k) (wnf_xiS hm) (by simp [summands]), ?_⟩
  simp [fr, xiS_lt_M]

theorem virtK_mono (hm : 1 ≤ m) (k : Nat) : Lt (virtK m k) (virtK m (k + 1)) := by
  have hAA := virtA_mono hm k
  have hK1 := wnf_virtK hm (k + 1)
  rw [virtK_eq, virtK_eq]
  refine (lt_xi_xi0 (Lt.ne hAA)).mpr (Or.inl ⟨hAA, ?_⟩)
  have hS := xiS_lt_virtK hm (k + 1)
  rw [virtK_eq] at hS hK1
  exact inC_virtA hm (zero_lt (virtA_ne_zero hm (k + 1))) k
    (fun j hj => lt_of_lt_of_leY (virtE_F hm j) (virtE_F hm (k + 1)) (virtA_F hm (k + 1))
      (virtE_lt_of hm (by omega)) (virtE_le_A hm (k + 1)))
    (inC_of_lt_cut (Cut.of_wnf hK1) _ (wnf_xiS hm) hS)

theorem inC_virtK (hm : 1 ≤ m) {g d : Tm} (hg : WNF g) (hS : Lt (succM m) g) (k : Nat) :
    inC (virtK m k) g d = true := by
  rw [virtK_eq]
  have hSF := WNF.succM hm
  have h0 : Lt .zero g := lt_transY WNF.zero hSF hg (zero_lt (by intro e; cases e)) hS
  have hg0 : g ≠ .zero := by intro e; rw [e] at h0; exact not_lt_zero _ h0
  refine inC_xi_iff.mpr (Or.inr ⟨inC_virtA hm h0 k
    (fun j _ => lt_transY (virtE_F hm j) hSF hg (virtE_lt hm j) hS)
    (inC_xi_iff.mpr (Or.inr ⟨inC_succM hg0, hS⟩)),
    lt_transY (virtA_F hm k) hSF hg (virtA_lt hm k) hS⟩)

theorem inC_xiS (hm : 1 ≤ m) {g d : Tm} (hg : WNF g) (hS : Lt (succM m) g) :
    inC (.Xi m (succM m)) g d = true := by
  have h0 : Lt .zero g := lt_transY WNF.zero (WNF.succM hm) hg (zero_lt (by intro e; cases e)) hS
  have hg0 : g ≠ .zero := by intro e; rw [e] at h0; exact not_lt_zero _ h0
  exact inC_xi_iff.mpr (Or.inr ⟨inC_succM hg0, hS⟩)

/-- `M_m` 未満の標準形は全てどれかの `virtK m n` 未満 -/
theorem virt_all (hm : 1 ≤ m) : ∀ z, WNF z → Lt z (.M m) → ∃ n, Lt z (virtK m n) := by
  have hMF := WNF.M' hm
  have hKF := wnf_virtK hm
  have hKm := virtK_mono hm
  have hOF : ∀ k, IsOF (virtK m k) := fun k => by rw [virtK_eq]; exact Or.inl ⟨_, _, rfl⟩
  have hlev : ∀ k, lev (virtK m k) = m := fun _ => rfl
  intro z
  induction z using size_induction with
  | h z ih =>
  intro hz hzM
  have hlz : lev z ≤ m := lev_le_of_lt_MY hm hz hzM
  rcases Nat.lt_or_eq_of_le hlz with hl | hl
  · exact ⟨0, lt_of_lev_lt' (by rw [hlev 0]; exact hl)⟩
  cases z with
  | zero => simp only [lev] at hl; exfalso; omega
  | M j => exact ⟨0, bot_ltY rfl (by rw [hlev 0]; exact Nat.le_of_eq hl) (hOF 0).principal (hOF 0).not_bot
      (hKF 0)⟩
  | plus a b =>
    obtain ⟨ha, -, -, -⟩ := hz.plus
    obtain ⟨k, hk⟩ := ih a (by simp only [Tm.size]; omega) ha (lt_transY ha hz hMF (lt_plus_leftY hz) hzM)
    exact ⟨k, (lt_plus_prin_iffY hz (hOF k).principal).mpr hk⟩
  | Om e =>
    have heF := hz.om.1
    obtain ⟨k, hk⟩ := ih e (by simp only [Tm.size]; omega) heF
      (lt_transY heF hz hMF (lt_om_selfY hz) hzM)
    exact ⟨k, (lt_om_OFG (hOF k) (hKF k)).mpr hk⟩
  | Psi ρ a =>
    have hρF := hz.psi.piF
    obtain ⟨k, hk⟩ := ih ρ (by simp only [Tm.size]; omega) hρF (tgt_lt_M_of_psi hm hz hzM)
    exact ⟨k, lt_transY hz hρF (hKF k) (lt_psi_targetY hz) hk⟩
  | Xi j b =>
    simp only [lev] at hl
    subst hl
    obtain ⟨-, hbF, hbS, hbC⟩ := hz.xi
    rcases le_of_ne_gtY hbF (WNF.succM hm) hbS with e | hb
    · subst e
      exact ⟨0, xiS_lt_virtK hm 0⟩
    -- `b < M_m⁺`
    obtain ⟨n, hn⟩ := virtG_hull hm hbF hb b hbF hb hbC
    obtain ⟨N, hN⟩ := exists_bound (P := fun _ => True) hKF hKm (fr (.M j) b)
      (fun w hw => hbF.of_mem_subs (fr_spec hw).1)
      (fun w hw _ => ih w (by
          have := size_le_of_mem_subs (fr_spec hw).1
          simp only [Tm.size]; omega)
        (hbF.of_mem_subs (fr_spec hw).1) (fr_spec hw).2)
    have hbA : Lt b (virtA j (max (n + 1) N)) :=
      lt_of_lt_of_leY hbF (virtA_F hm (n + 1)) (virtA_F hm _)
        (lt_of_lt_of_leY hbF (virtE_F hm (n + 1)) (virtA_F hm (n + 1))
          (lt_of_lt_of_leY hbF (virtG_F hm (n + 1)) (virtE_F hm (n + 1)) hn (le_virtG_virtE hm _))
          (virtE_le_A hm (n + 1)))
        (virtA_le_of hm (Nat.le_max_left _ _))
    refine ⟨max (n + 1) N, ?_⟩
    have hy := hKF (max (n + 1) N)
    rw [virtK_eq] at hy ⊢
    exact xi_step hz hy hbA (fun w hw => by
      have h1 := hN w hw trivial
      have h2 := seq_mono_le hKF hKm (Nat.le_max_right (n + 1) N)
      rw [virtK_eq] at h2
      exact lt_of_lt_of_leY (hbF.of_mem_subs (fr_spec hw).1) (hKF N) hy h1 h2)

end Virt

end MahloOCF.FS
