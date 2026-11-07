import Mahlo.Gen
import Mahlo.Notation

/-! 項の値と、標準形の意味論版 `Good`。

* `val`：項の値（`Ψ_π(a)` は `Psi (val π) (val a)`、`Ξ_n(a)` は `Xi n (val a)`）。
* `Good`：`MahloOCF.isNF` と同じ形の帰納的述語で、`isNF` が `cmp`・`inC` で調べる条件を
  順序数の条件に置き換えたもの。`Ψ_π(a)` には崩壊先の有効性（`π = Ξ_m(d)` なら `d < a`）と
  正規性 `a ∈ C(a, Ψ_π(a))` を課す。
* `Good.inv`：`Good` な項の値の性質（`Inv`：Cantor 標準形、階、正則な崩壊先、`Ω` の不動点など）。
* `val_inj`：`Good` な項の上で `val` は単射。 -/

namespace OCF.Mahlo

universe u

open Ordinal Rathjen MahloOCF

noncomputable section

variable [Setting.{u}]

/-- 項の値 -/
def val : Tm → Ordinal.{u}
  | .zero => 0
  | .M n => K n
  | .plus a b => val a + val b
  | .Om a => Om (val a)
  | .Xi n a => Xi n (val a)
  | .Psi pi a => Psi (val pi) (val a)

theorem val_one : val.{u} one = succ 0 := Psi_Om_zero_zero

/-! ### 構文についての補題 -/

theorem summands_eq_nil {t : Tm} : summands t = [] ↔ t = .zero := by
  cases t <;> simp [summands]

theorem ne_zero_of_isPrincipal {t : Tm} (h : isPrincipal t = true) : t ≠ .zero := by
  intro e; subst e; simp [isPrincipal] at h

theorem ne_zero_of_isRegTerm {t : Tm} (h : isRegTerm t = true) : t ≠ .zero := by
  intro e; subst e; simp [isRegTerm] at h

theorem isPrincipal_of_isRegTerm {t : Tm} (h : isRegTerm t = true) : isPrincipal t = true := by
  cases t <;> simp_all [isRegTerm, isPrincipal]

theorem CNF.append_left {α : Ordinal.{u}} {l₁ l₂ : List Ordinal.{u}} (h : CNF α (l₁ ++ l₂)) :
    CNF (listSum l₁) l₁ :=
  ⟨fun p hp => h.1 p (List.mem_append_left l₂ hp), (List.pairwise_append.mp h.2.1).1, rfl⟩

/-- 加法的主数でない順序数は `Ω` の不動点でない -/
theorem lt_Om_of_not_principal {x : Ordinal.{u}} (hΛ : x < Λ) (h : ¬ IsPrincipal x) :
    x < Om x := by
  apply lt_of_le_of_ne (le_Om hΛ)
  intro e
  apply h
  rw [e]
  exact Om_principal hΛ

/-- 標準形の意味論版 -/
inductive Good : Tm → Prop
  | zero : Good .zero
  | M (n : Nat) (hn : 1 ≤ n) : Good (.M n)
  | plus (a b : Tm) (ha : Good a) (hb : Good b) (hap : isPrincipal a = true)
      (hb0 : b ≠ .zero) (hle : ∀ h, (summands b).head? = some h → val.{u} h ≤ val a) :
      Good (.plus a b)
  | om (a : Tm) (ha : Good a) (hf : omegaFixed a = false) : Good (.Om a)
  | xi (n : Nat) (a : Tm) (hn : 1 ≤ n) (ha : Good a) (hcap : val.{u} a ≤ capK n)
      (hC : C (val.{u} a) (K n) (val a)) :
      Good (.Xi n a)
  | psi (pi a : Tm) (hpi : Good pi) (ha : Good a) (hreg : isRegTerm pi = true)
      (hact : ∀ m d, pi = .Xi m d → val.{u} d < val a)
      (hnorm : C (val.{u} a) (Psi (val pi) (val a)) (val a)) : Good (.Psi pi a)

/-- `Good` な項の値の性質 -/
structure Inv (t : Tm) : Prop where
  lt_Λ : val.{u} t < Λ
  cnf : CNF (val.{u} t) ((summands t).map val)
  bounds : t ≠ .zero → 1 ≤ lev t ∧ K (lev t - 1) ≤ val.{u} t ∧ val.{u} t < K (lev t)
  strict : isPrincipal t = true → (∀ n, t ≠ .M n) → K (lev t - 1) < val.{u} t
  fixed : omegaFixed t = true → Om (val.{u} t) = val t
  nonfixed : omegaFixed t = false → val.{u} t < Om (val t)
  reg : isRegTerm t = true → RegTarget (val.{u} t)
  om : ∀ c, t = .Om c → isSucc c = true → ∃ ζ, val.{u} c = succ ζ ∧ succ ζ < Λ
  xi : ∀ n a, t = .Xi n a → Xi n (val.{u} a) < K n ∧ val.{u} a ≤ capK n
  psi : ∀ pi a, t = .Psi pi a → Psi (val.{u} pi) (val a) < val pi

theorem Inv.pos {t : Tm} (h : Inv.{u} t) (ht : t ≠ .zero) : 0 < val.{u} t := by
  have hc := h.cnf
  cases hs : summands t with
  | nil => exact absurd (summands_eq_nil.mp hs) ht
  | cons p l =>
    rw [hs, List.map_cons] at hc
    exact hc.pos

theorem Inv.principal {t : Tm} (h : Inv.{u} t) (hp : isPrincipal t = true) :
    IsPrincipal (val.{u} t) := by
  have hc := h.cnf
  rw [summands_principal hp, List.map_cons, List.map_nil] at hc
  exact hc.head_principal

/-- `c` の最後の項が `1` なら `val c = ζ + 1` -/
theorem Inv.isSucc {c : Tm} (h : Inv.{u} c) (hs : isSucc c = true) :
    ∃ ζ, val.{u} c = succ ζ := by
  obtain ⟨ys, hys⟩ := summands_of_isSucc hs
  have hc := h.cnf
  rw [hys, List.map_append, List.map_cons, List.map_nil] at hc
  refine Exists.intro (listSum (ys.map val)) ?_
  rw [hc.eq, listSum_append, listSum_cons, listSum_nil, add_zero, val_one]
  exact add_one_eq_succ _

theorem K_isPrincipal {n : Nat} (hn : 1 ≤ n) : IsPrincipal (K.{u} n) := (R_K hn).2.isPrincipal

/-- `Good` な項の値の性質 -/
theorem Good.inv {t : Tm} (h : Good.{u} t) : Inv.{u} t := by
  induction h with
  | zero =>
    exact {
      lt_Λ := Λ_pos
      cnf := cnf_zero
      bounds := fun h => absurd rfl h
      strict := fun h => by simp [isPrincipal] at h
      fixed := fun h => by simp [omegaFixed] at h
      nonfixed := fun _ => Om_pos Λ_pos
      reg := fun h => by simp [isRegTerm] at h
      om := fun _ h => by cases h
      xi := fun _ _ h => by cases h
      psi := fun _ _ h => by cases h }
  | M n hn =>
    exact {
      lt_Λ := K_lt_Λ n
      cnf := cnf_single (K_isPrincipal hn)
      bounds := fun _ => by
        refine ⟨Nat.le_add_left 1 n, ?_, K_lt (Nat.lt_succ_self n)⟩
        show K (n + 1 - 1) ≤ K n
        rw [Nat.add_sub_cancel]
        exact le_refl _
      strict := fun _ h => absurd rfl (h n)
      fixed := fun _ => Om_K hn
      nonfixed := fun h => by simp [omegaFixed] at h
      reg := fun h => by simp [isRegTerm] at h
      om := fun _ h => by cases h
      xi := fun _ _ h => by cases h
      psi := fun _ _ h => by cases h }
  | plus a b _ _ hap hb0 hle iha ihb =>
    have ha0 := ne_zero_of_isPrincipal hap
    have hcnf : CNF (val.{u} (.plus a b)) ((summands (.plus a b)).map val) := by
      rw [summands_plus, List.map_cons]
      have hb := ihb.cnf
      refine ⟨?_, ?_, ?_⟩
      · intro p hp
        cases List.mem_cons.mp hp with
        | inl e => rw [e]; exact iha.principal hap
        | inr hp => exact hb.principal hp
      · apply List.pairwise_cons.mpr (And.intro ?_ hb.2.1)
        intro q hq
        cases hs : summands b with
        | nil => exact absurd (summands_eq_nil.mp hs) hb0
        | cons h l =>
          rw [hs, List.map_cons] at hq hb
          exact le_trans (hb.mem_le_head hq) (hle h (by rw [hs]; rfl))
      · show val a + val b = _
        rw [listSum_cons, ← hb.eq]
    have hbd := iha.bounds ha0
    have hlt : val.{u} (.plus a b) < K (lev (.plus a b)) := by
      have hc := hcnf
      rw [summands_plus, List.map_cons] at hc
      exact hc.lt_of_head_lt (K_isPrincipal hbd.1) hbd.2.2
    have hΛ : val.{u} (.plus a b) < Λ := lt_trans _ _ _ hlt (K_lt_Λ _)
    have hnp : ¬ IsPrincipal (val.{u} (.plus a b)) := by
      intro hP
      have hc := hcnf
      rw [summands_plus, List.map_cons] at hc
      have h2 := (List.cons.inj (cnf_of_principal hP hc)).2
      exact absurd (summands_eq_nil.mp (List.map_eq_nil_iff.mp h2)) hb0
    exact {
      lt_Λ := hΛ
      cnf := hcnf
      bounds := fun _ => ⟨hbd.1, le_trans hbd.2.1 (le_add _ _), hlt⟩
      strict := fun h => by simp [isPrincipal] at h
      fixed := fun h => by simp [omegaFixed] at h
      nonfixed := fun _ => lt_Om_of_not_principal hΛ hnp
      reg := fun h => by simp [isRegTerm] at h
      om := fun _ h => by cases h
      xi := fun _ _ h => by cases h
      psi := fun _ _ h => by cases h }
  | om a _ hf iha =>
    have hΛ := iha.lt_Λ
    have hlt : val.{u} a < Om (val a) := iha.nonfixed hf
    have hOΛ : Om (val.{u} a) < Λ := Om_lt_Λ hΛ
    have hbd : 1 ≤ lev (.Om a) ∧ K (lev (.Om a) - 1) ≤ val.{u} a ∧
        Om (val.{u} a) < K (lev (.Om a)) := by
      by_cases ha0 : a = .zero
      · subst ha0
        exact ⟨Nat.le_refl 1, zero_le _, Om_zero_lt_K (Nat.le_refl 1)⟩
      · have hb := iha.bounds ha0
        have e : lev (.Om a) = lev a := by simp only [lev]; omega
        rw [e]
        exact ⟨hb.1, hb.2.1, Om_lt_K hb.1 hb.2.2⟩
    exact {
      lt_Λ := hOΛ
      cnf := cnf_single (Om_principal hΛ)
      bounds := fun _ => ⟨hbd.1, le_trans hbd.2.1 (Or.inl hlt), hbd.2.2⟩
      strict := fun _ _ => lt_of_le_of_lt hbd.2.1 hlt
      fixed := fun h => by simp [omegaFixed] at h
      nonfixed := fun _ => Om_lt_Om hlt hOΛ
      reg := fun hr => by
        simp only [isRegTerm, Bool.or_eq_true, beq_iff_eq] at hr
        cases hr with
        | inl h0 => subst h0; exact Or.inl rfl
        | inr hs =>
          obtain ⟨ζ, hζ⟩ := iha.isSucc hs
          have hsΛ : succ ζ < Λ := by rw [← hζ]; exact hΛ
          exact Or.inr (Or.inl ⟨ζ, hsΛ, by show Om (val a) = _; rw [hζ]⟩)
      om := fun c h hs => by
        cases h
        obtain ⟨ζ, hζ⟩ := iha.isSucc hs
        exact ⟨ζ, hζ, by rw [← hζ]; exact hΛ⟩
      xi := fun _ _ h => by cases h
      psi := fun _ _ h => by cases h }
  | xi n a hn _ hcap hC _ =>
    have hX : Xi n (val.{u} a) < K n := Xi_lt hn hC
    have g := xiGood_of_lt hX
    exact {
      lt_Λ := lt_trans _ _ _ hX (K_lt_Λ n)
      cnf := cnf_single g.R.2.isPrincipal
      bounds := fun _ => ⟨hn, Or.inl g.gt, hX⟩
      strict := fun _ _ => g.gt
      fixed := fun _ => g.fixed
      nonfixed := fun h => by simp [omegaFixed] at h
      reg := fun _ => Or.inr (Or.inr ⟨n, val a, hcap, rfl, hX⟩)
      om := fun _ h => by cases h
      xi := fun _ _ h => by cases h; exact ⟨hX, hcap⟩
      psi := fun _ _ h => by cases h }
  | psi pi a _ _ hreg hact _ ihpi _ =>
    have hRT := ihpi.reg hreg
    have hR := hRT.isReg
    have hψ : Psi (val.{u} pi) (val a) < val pi := by
      cases pi with
      | Om c =>
        simp only [isRegTerm, Bool.or_eq_true, beq_iff_eq] at hreg
        cases hreg with
        | inl h0 => subst h0; exact Psi_Om_zero_lt _
        | inr hs =>
          obtain ⟨ζ, hζ, hsΛ⟩ := ihpi.om c rfl hs
          show Psi (Om (val c)) (val a) < Om (val c)
          rw [hζ]
          exact Psi_Om_succ_lt hsΛ _
      | Xi m d => exact Psi_Xi_lt (ihpi.xi m d rfl).1 (ihpi.xi m d rfl).2 (hact m d rfl)
      | _ => simp [isRegTerm] at hreg
    have sp := Psi_spec hψ
    have hbd := ihpi.bounds (ne_zero_of_isRegTerm hreg)
    have hKψ : K (lev pi - 1) < Psi (val.{u} pi) (val a) := by
      apply sp.2 _ (C_K _ _ _)
      cases hbd.2.1 with
      | inl h => exact h
      | inr e => exact absurd e.symm (hR.2.2 _)
    exact {
      lt_Λ := lt_trans _ _ _ hψ ihpi.lt_Λ
      cnf := cnf_single (Psi_principal_of_lt hR.1 hψ)
      bounds := fun _ => ⟨hbd.1, Or.inl hKψ, lt_trans _ _ _ hψ hbd.2.2⟩
      strict := fun _ _ => hKψ
      fixed := fun hf => by
        cases pi with
        | Xi m d => exact Psi_fixed hψ (ihpi.fixed rfl) ihpi.lt_Λ
        | _ => simp [omegaFixed, isXi] at hf
      nonfixed := fun hf => by
        cases pi with
        | Om c =>
          simp only [isRegTerm, Bool.or_eq_true, beq_iff_eq] at hreg
          cases hreg with
          | inl h0 => subst h0; exact Psi_Om_zero_lt_Om _
          | inr hs =>
            obtain ⟨ζ, hζ, hsΛ⟩ := ihpi.om c rfl hs
            show Psi (Om (val c)) (val a) < Om (Psi (Om (val c)) (val a))
            rw [hζ]
            exact Psi_Om_succ_lt_Om hsΛ _
        | Xi m d => simp [omegaFixed, isXi] at hf
        | _ => simp [isRegTerm] at hreg
      reg := fun h => by simp [isRegTerm] at h
      om := fun _ h => by cases h
      xi := fun _ _ h => by cases h
      psi := fun _ _ h => by cases h; exact hψ }

/-! ### 補助的な項 -/

theorem good_one : Good.{u} one := by
  refine Good.psi _ _ (Good.om _ Good.zero rfl) Good.zero rfl (fun _ _ h => by cases h) ?_
  show C 0 (Psi (Om 0) 0) 0
  exact C_zero _ _

theorem good_kTerm (m : Nat) : Good.{u} (kTerm m) ∧ val.{u} (kTerm m) = K m := by
  unfold kTerm
  split
  · rename_i h; subst h; exact ⟨Good.zero, rfl⟩
  · rename_i h; exact ⟨Good.M m (Nat.pos_of_ne_zero h), rfl⟩

/-- `M_n^+ = Ω_{M_n + 1}` の項 -/
theorem good_succM {n : Nat} (hn : 1 ≤ n) :
    Good.{u} (succM n) ∧ val.{u} (succM n) = capK n := by
  have h1 : val.{u} one ≤ val (.M n) := by
    rw [val_one]
    exact Or.inl (lt_trans _ _ _ one_lt_Om_zero (Om_zero_lt_K hn))
  refine ⟨Good.om _ (Good.plus _ _ (Good.M n hn) good_one rfl (fun h => by cases h) ?_) rfl, ?_⟩
  · intro h hh
    simp only [summands_principal (rfl : isPrincipal one = true), List.head?_cons,
      Option.some.injEq] at hh
    subst hh
    exact h1
  · show Om (K n + val one) = Om (K n + succ 0)
    rw [val_one]

theorem good_omOf {ζ : Tm} (h : Good.{u} ζ) : Good.{u} (omOf ζ) ∧ val.{u} (omOf ζ) = Om (val ζ) := by
  unfold omOf
  split
  · rename_i hf; exact ⟨h, (h.inv.fixed hf).symm⟩
  · rename_i hf
    exact ⟨Good.om ζ h (by simpa using hf), rfl⟩

theorem summands_good : ∀ (t : Tm), Good.{u} t →
    ∀ s, s ∈ summands t → Good.{u} s ∧ isPrincipal s = true := by
  intro t
  induction t with
  | zero => intro _ s hs; simp [summands] at hs
  | plus a b _ ihb =>
    intro h s hs
    cases h with
    | plus _ _ ha hb hap _ _ =>
      rw [summands_plus] at hs
      cases List.mem_cons.mp hs with
      | inl e => rw [e]; exact ⟨ha, hap⟩
      | inr hs => exact ihb hb s hs
  | _ =>
    intro h s hs
    simp only [summands, List.mem_singleton] at hs
    rw [hs]
    exact ⟨h, rfl⟩

theorem summands_ofSummands : ∀ (l : List Tm), (∀ s, s ∈ l → isPrincipal s = true) →
    summands (ofSummands l) = l
  | [], _ => rfl
  | [a], h => summands_principal (h a List.mem_cons_self)
  | a :: b :: rest, h => by
    show a :: summands (ofSummands (b :: rest)) = a :: b :: rest
    rw [summands_ofSummands (b :: rest) (fun s hs => h s (List.mem_cons_of_mem a hs))]

theorem val_ofSummands : ∀ (l : List Tm), val.{u} (ofSummands l) = listSum (l.map val)
  | [] => rfl
  | [a] => by
    show val a = listSum [val a]
    rw [listSum_cons, listSum_nil, add_zero]
  | a :: b :: rest => by
    show val a + val (ofSummands (b :: rest)) = listSum (val a :: (b :: rest).map val)
    rw [val_ofSummands (b :: rest), listSum_cons]

theorem ofSummands_ne_zero : ∀ (l : List Tm), l ≠ [] → (∀ s, s ∈ l → isPrincipal s = true) →
    ofSummands l ≠ .zero
  | [], h, _ => absurd rfl h
  | [a], _, hp => ne_zero_of_isPrincipal (hp a List.mem_cons_self)
  | _ :: _ :: _, _, _ => by intro e; cases e

/-- 標準形の和の先頭部分は標準形 -/
theorem good_prefix : ∀ (t : Tm), Good.{u} t → ∀ (l l' : List Tm), summands t = l ++ l' →
    l ≠ [] → Good.{u} (ofSummands l) := by
  intro t
  induction t with
  | zero => intro _ l l' hs hl; simp [summands] at hs; exact absurd hs.1 hl
  | plus a b _ ihb =>
    intro h l l' hs hl
    cases h with
    | plus _ _ ha hb hap hb0 hle =>
      rw [summands_plus] at hs
      cases l with
      | nil => exact absurd rfl hl
      | cons x l₁ =>
        rw [List.cons_append] at hs
        have ex := (List.cons.inj hs).1
        have hsb := (List.cons.inj hs).2
        subst ex
        cases l₁ with
        | nil => exact ha
        | cons y r =>
          have gl₁ := ihb hb (y :: r) l' hsb (by intro e; cases e)
          have hprin : ∀ s, s ∈ y :: r → isPrincipal s = true := fun s hs' =>
            (summands_good b hb s (by rw [hsb]; exact List.mem_append_left _ hs')).2
          show Good (.plus _ (ofSummands (y :: r)))
          refine Good.plus _ _ ha gl₁ hap (ofSummands_ne_zero _ (by intro e; cases e) hprin) ?_
          intro h' hh
          rw [summands_ofSummands _ hprin] at hh
          apply hle h'
          rw [hsb]
          simp only [List.cons_append, List.head?_cons] at hh ⊢
          exact hh
  | _ =>
    intro h l l' hs hl
    simp only [summands] at hs
    cases l with
    | nil => exact absurd rfl hl
    | cons x l₁ =>
      rw [List.cons_append] at hs
      have ex := (List.cons.inj hs).1
      have e2 := (List.cons.inj hs).2
      have hl₁ : l₁ = [] := (List.append_eq_nil_iff.mp e2.symm).1
      subst hl₁
      rw [← ex]
      exact h

/-- `c` の最後の項が `1` なら `c = predT c + 1` -/
theorem good_predT {c : Tm} (h : Good.{u} c) (hs : isSucc c = true) :
    Good.{u} (predT c) ∧ val.{u} c = succ (val (predT c)) := by
  obtain ⟨ys, hys⟩ := summands_of_isSucc hs
  rw [predT_of_summands hys]
  have hval : val.{u} c = succ (val (ofSummands ys)) := by
    have hc := h.inv.cnf
    rw [hys, List.map_append, List.map_cons, List.map_nil] at hc
    rw [hc.eq, listSum_append, listSum_cons, listSum_nil, add_zero, val_one, val_ofSummands]
    exact add_one_eq_succ _
  refine And.intro ?_ hval
  cases ys with
  | nil => exact Good.zero
  | cons y r => exact good_prefix c h (y :: r) [one] hys (by intro e; cases e)

/-! ### `val` の単射性 -/

theorem summands_val_eq {a b : Tm} (ha : Inv.{u} a) (hb : Inv.{u} b) (e : val.{u} a = val b) :
    (summands a).map val.{u} = (summands b).map val := by
  have h := hb.cnf
  rw [← e] at h
  exact cnf_unique ha.cnf h

/-- 和でない項と値が等しい項は和でない -/
theorem isPrincipal_of_val_eq {a b : Tm} (ha : Good.{u} a) (hb : Good.{u} b)
    (hap : isPrincipal a = true) (e : val.{u} a = val b) : isPrincipal b = true := by
  have hs := summands_val_eq ha.inv hb.inv e
  rw [summands_principal hap, List.map_cons, List.map_nil] at hs
  cases hb with
  | zero => simp [summands] at hs
  | plus b₁ b₂ _ _ _ hb0 _ =>
    rw [summands_plus, List.map_cons] at hs
    have h2 := (List.cons.inj hs).2
    exact absurd (summands_eq_nil.mp (List.map_eq_nil_iff.mp h2.symm)) hb0
  | _ => simp [isPrincipal]

/-- `Good` な項の上で `val` は単射 -/
theorem val_inj : ∀ (a b : Tm), Good.{u} a → Good.{u} b → val.{u} a = val b → a = b := by
  intro a
  induction a with
  | zero =>
    intro b _ hb e
    have hs := summands_val_eq Good.zero.inv hb.inv e
    simp only [summands, List.map_nil] at hs
    exact (summands_eq_nil.mp (List.map_eq_nil_iff.mp hs.symm)).symm
  | plus a₁ a₂ ih₁ ih₂ =>
    intro b ha hb e
    have hs := summands_val_eq ha.inv hb.inv e
    by_cases hbp : isPrincipal b = true
    · have h := isPrincipal_of_val_eq hb ha hbp e.symm
      simp [isPrincipal] at h
    cases ha with
    | plus _ _ ha₁ ha₂ _ _ _ =>
      cases hb with
      | plus b₁ b₂ hb₁ hb₂ _ _ _ =>
        rw [summands_plus, summands_plus, List.map_cons, List.map_cons] at hs
        have e₁ := (List.cons.inj hs).1
        have e₂ : val.{u} a₂ = val b₂ := by
          rw [ha₂.inv.cnf.eq, hb₂.inv.cnf.eq, (List.cons.inj hs).2]
        rw [ih₁ b₁ ha₁ hb₁ e₁, ih₂ b₂ ha₂ hb₂ e₂]
      | zero => simp [summands] at hs
      | _ => simp [isPrincipal] at hbp
  | M n =>
    intro b ha hb e
    have hbp := isPrincipal_of_val_eq ha hb rfl e
    have ib := hb.inv
    cases ha with
    | M _ _ =>
      cases hb with
      | M m _ => rw [K_inj e]
      | om c hc hf => exact absurd e.symm (Om_ne_K hc.inv.lt_Λ (hc.inv.nonfixed hf))
      | xi m c _ _ _ _ => exact absurd e.symm (Xi_ne_K (ib.xi m c rfl).1)
      | psi π β _ _ _ _ _ => exact absurd e.symm (Psi_ne_K (ib.psi π β rfl))
      | _ => simp [isPrincipal] at hbp
  | Om a ih =>
    intro b ha hb e
    have hbp := isPrincipal_of_val_eq ha hb rfl e
    have ib := hb.inv
    cases ha with
    | om _ ha' hf =>
      have hΛ := ha'.inv.lt_Λ
      have hlt := ha'.inv.nonfixed hf
      cases hb with
      | M m _ => exact absurd e (Om_ne_K hΛ hlt)
      | om c hc _ => rw [ih c ha' hc (Om_inj hΛ hc.inv.lt_Λ e)]
      | xi m c _ _ _ _ => exact absurd e (Om_ne_Xi hΛ hlt (ib.xi m c rfl).1)
      | psi π β _ _ _ _ _ => exact absurd e (Om_ne_Psi hΛ hlt (ib.psi π β rfl))
      | _ => simp [isPrincipal] at hbp
  | Xi n a ih =>
    intro b ha hb e
    have hbp := isPrincipal_of_val_eq ha hb rfl e
    have ia := ha.inv
    have ib := hb.inv
    have hx := ia.xi n a rfl
    cases ha with
    | xi _ _ _ ha' _ _ =>
      cases hb with
      | M m _ => exact absurd e (Xi_ne_K hx.1)
      | om c hc hf => exact absurd e.symm (Om_ne_Xi hc.inv.lt_Λ (hc.inv.nonfixed hf) hx.1)
      | xi m c _ hc _ _ =>
        have h := Xi_inj' hx.1 (ib.xi m c rfl).1 hx.2 (ib.xi m c rfl).2 e
        rw [h.1, ih c ha' hc h.2]
      | psi π β _ _ _ _ _ => exact absurd e.symm (Xi_ne_Psi hx.1 hx.2 (ib.psi π β rfl))
      | _ => simp [isPrincipal] at hbp
  | Psi pi a ihpi iha =>
    intro b ha hb e
    have hbp := isPrincipal_of_val_eq ha hb rfl e
    have ia := ha.inv
    have ib := hb.inv
    have hp := ia.psi pi a rfl
    cases ha with
    | psi _ _ hpi ha' _ _ hn =>
      cases hb with
      | M m _ => exact absurd e (Psi_ne_K hp)
      | om c hc hf => exact absurd e.symm (Om_ne_Psi hc.inv.lt_Λ (hc.inv.nonfixed hf) hp)
      | xi m c _ _ _ _ => exact absurd e (Xi_ne_Psi (ib.xi m c rfl).1 (ib.xi m c rfl).2 hp)
      | psi π β hπ hβ _ _ hn' =>
        have h := Psi_inj hp (ib.psi π β rfl) hn hn' e
        rw [ihpi π hpi hπ h.1, iha β ha' hβ h.2]
      | _ => simp [isPrincipal] at hbp

end

end OCF.Mahlo
