import Mahlo.Succ

/-! 等号の定理と、弱 Mahlo 基数の列からの結論。

* `nfValue_iff_C`：`x` が標準形の値 ⟺ `x ∈ C(Λ, 0)`（崩壊関数の閉包）。標準形は一意（`val_inj_of_isNF`）。
* `settingOfMahlo`：弱 Mahlo 基数の列（`∀ n, EnumDef WeaklyMahlo (ordNat n)`）から `Setting` を作る。
* `wellFounded_lt`：弱 Mahlo 基数の列があれば、標準形の上の `MahloOCF.lt` は整礎。
* `lt_isStrictTotalOrder`：標準形の上の `MahloOCF.lt` は狭義全順序。 -/

namespace OCF.Mahlo

universe u

open Ordinal Rathjen MahloOCF

noncomputable section

/-- `p` が極限なら `x + p` も極限 -/
theorem isLimit_add {p : Ordinal.{u}} (x : Ordinal.{u}) (hp : IsLimit p) : IsLimit (x + p) := by
  refine ⟨lt_of_lt_of_le hp.1 (right_le_add x p), ?_⟩
  intro γ hγ
  by_cases hγx : γ < x
  · exact lt_of_le_of_lt (succ_le_of_lt hγx) (lt_add_of_pos x hp.1)
  · obtain ⟨d, hd, e⟩ := le_add_cases x p γ (Or.inl hγ) hγx
    have hdp : d < p := by
      cases hd with
      | inl h => exact h
      | inr h => rw [e, h] at hγ; exact absurd hγ (lt_irrefl _)
    rw [e, ← add_succ]
    exact (add_lt_add_iff_right x).mpr (hp.2 d hdp)

variable [Setting.{u}]

theorem exists_terms {Q : Tm → Prop} : ∀ l : List Ordinal.{u},
    (∀ p, p ∈ l → ∃ t, Q t ∧ val.{u} t = p) →
    ∃ ts : List Tm, (∀ t, t ∈ ts → Q t) ∧ ts.map val.{u} = l
  | [], _ => ⟨[], fun _ h => absurd h List.not_mem_nil, rfl⟩
  | p :: l, h => by
    obtain ⟨t, ht, e⟩ := h p List.mem_cons_self
    obtain ⟨ts, hts, e'⟩ := exists_terms l (fun q hq => h q (List.mem_cons_of_mem p hq))
    refine ⟨t :: ts, ?_, ?_⟩
    · intro s hs
      cases List.mem_cons.mp hs with
      | inl e => rw [e]; exact ht
      | inr hs => exact hts s hs
    · rw [List.map_cons, e, e']

/-- 加法的主数の標準形の非増加列から和の標準形を作る -/
theorem good_ofSummands : ∀ l : List Tm,
    (∀ s, s ∈ l → Good.{u} s ∧ isPrincipal s = true) → Nonincr (l.map val.{u}) →
    Good.{u} (ofSummands l) ∧ val.{u} (ofSummands l) = listSum (l.map val)
  | [], _, _ => ⟨Good.zero, rfl⟩
  | [a], h, _ => by
    refine ⟨(h a List.mem_cons_self).1, ?_⟩
    show val a = listSum [val a]
    rw [listSum_cons, listSum_nil, add_zero]
  | a :: b :: rest, h, hn => by
    have ha := h a List.mem_cons_self
    have hrest : ∀ s, s ∈ b :: rest → Good.{u} s ∧ isPrincipal s = true :=
      fun s hs => h s (List.mem_cons_of_mem a hs)
    have hn2 : (val.{u} a :: (b :: rest).map val).Pairwise (fun x y => y ≤ x) := hn
    have ih := good_ofSummands (b :: rest) hrest (List.pairwise_cons.mp hn2).2
    have hsum := summands_ofSummands (b :: rest) (fun s hs => (hrest s hs).2)
    refine ⟨?_, ?_⟩
    · show Good (.plus a (ofSummands (b :: rest)))
      refine Good.plus a _ ha.1 ih.1 ha.2 ?_ ?_
      · intro e
        have h0 := summands_eq_nil.mpr e
        rw [hsum] at h0
        cases h0
      · intro hd hhd
        rw [hsum] at hhd
        simp only [List.head?_cons, Option.some.injEq] at hhd
        subst hhd
        exact (List.pairwise_cons.mp hn2).1 (val b) List.mem_cons_self
    · show val a + val (ofSummands (b :: rest)) = listSum (val a :: (b :: rest).map val)
      rw [ih.2, listSum_cons]

/-! ### 標準形の値は `C(Λ, 0)` に入る -/

theorem C_of_good {t : Tm} (h : Good.{u} t) : C Λ 0 (val.{u} t) := by
  induction h with
  | zero => exact C_zero _ _
  | M n _ => exact C_K _ _ n
  | plus _ _ _ _ _ _ _ iha ihb => exact C_add iha ihb
  | om a ha _ iha => exact C_Om ha.inv.lt_Λ iha
  | xi n a _ ha hc _ iha => exact C_Xi n ha.inv.lt_Λ hc iha
  | psi pi a hpi ha hreg hact hn ihpi iha =>
    have hψ := (Good.psi pi a hpi ha hreg hact hn).inv.psi pi a rfl
    exact C_Psi ha.inv.lt_Λ (hpi.inv.reg hreg).isReg hψ hn ihpi iha

/-! ### 正則な値の標準形 -/

/-- 最後の項が `1` でない 0 以外の標準形の値は極限 -/
theorem isLimit_of_not_isSucc {c : Tm} (hc : Good.{u} c) (hc0 : c ≠ .zero)
    (hs : isSucc c = false) : IsLimit (val.{u} c) := by
  have ic := hc.inv
  cases hl : (summands c).getLast? with
  | none => exact absurd (summands_eq_nil.mp (List.getLast?_eq_none_iff.mp hl)) hc0
  | some s =>
    obtain ⟨ys, hys⟩ := List.getLast?_eq_some_iff.mp hl
    have hsmem : s ∈ summands c := by
      rw [hys]
      exact List.mem_append_right _ List.mem_cons_self
    have gs := summands_good c hc s hsmem
    have hs1 : s ≠ one := by
      intro e
      subst e
      simp [isSucc, hl] at hs
    have is := gs.1.inv
    have hP := is.principal gs.2
    have h1 : succ 0 < val.{u} s := by
      apply lt_of_le_of_ne (succ_le_of_lt hP.pos)
      intro e
      apply hs1
      exact val_inj _ _ gs.1 good_one (by rw [val_one]; exact e.symm)
    have hlim := hP.isLimit h1
    have hcnf := ic.cnf
    rw [hys, List.map_append, List.map_cons, List.map_nil] at hcnf
    rw [hcnf.eq, listSum_append, listSum_cons, listSum_nil, add_zero]
    exact isLimit_add _ hlim

/-- `Ω` の引数が極限なら `Ω` は正則でない -/
theorem not_R_Om_of_isLimit {w : Ordinal.{u}} (hl : IsLimit w) (hΛ : w < Λ) (hlt : w < Om w) :
    ¬ R (Om w) := by
  intro hR
  have hcf : CofinalFrom w (Om w) := by
    refine ⟨fun x => Om (type ((representative w).below x)), ?_, ?_⟩
    · intro x
      exact Om_lt_Om (initial_lt w x) hΛ
    · rw [Om_limit hl hΛ]
      rfl
  have hle : cf (Om w) ≤ w := least_le (fun β => CofinalFrom β (Om w)) hcf
  rw [hR.2.2] at hle
  exact absurd hlt (not_lt_of_le hle)

/-- 値が崩壊先になる標準形は `isRegTerm` -/
theorem isRegTerm_of_good {t : Tm} (h : Good.{u} t) (hR : RegTarget (val.{u} t)) :
    isRegTerm t = true := by
  have it := h.inv
  have hreg := hR.isReg
  cases h with
  | zero => exact absurd hreg.1.1 (not_lt_of_le (zero_le _))
  | M n _ => exact absurd rfl (hreg.2.2 n)
  | plus a b _ _ _ hb0 _ =>
    exfalso
    have hc := it.cnf
    rw [summands_plus, List.map_cons] at hc
    have h2 := (List.cons.inj (cnf_of_principal hreg.1.2.isPrincipal hc)).2
    exact hb0 (summands_eq_nil.mp (List.map_eq_nil_iff.mp h2))
  | om c hc hf =>
    simp only [isRegTerm, Bool.or_eq_true, beq_iff_eq]
    by_cases hc0 : c = .zero
    · exact Or.inl hc0
    · right
      cases hs : isSucc c with
      | true => rfl
      | false =>
        exact absurd hreg.1
          (not_R_Om_of_isLimit (isLimit_of_not_isSucc hc hc0 hs) hc.inv.lt_Λ (hc.inv.nonfixed hf))
  | xi _ _ _ _ _ => rfl
  | psi pi a _ _ _ _ _ => exact absurd rfl (Psi_ne_regTarget (it.psi pi a rfl) hR)

/-! ### `C(Λ, 0)` の元は標準形の値 -/

theorem exists_good_of_Cn : ∀ n z, Cn Λ 0 n z → ∃ t, Good.{u} t ∧ val.{u} t = z := by
  intro n
  induction n using Nat.strongRecOn with
  | ind n ih =>
    have ihb : ∀ w, Below Λ 0 n w → ∃ t, Good.{u} t ∧ val.{u} t = w := by
      intro w hw
      obtain ⟨k, hk, hkw⟩ := hw
      exact ih k hk w hkw
    have hprin : ∀ p, Cn Λ 0 n p → IsPrincipal p →
        ∃ t, (Good.{u} t ∧ isPrincipal t = true) ∧ val.{u} t = p := by
      intro p hp hP
      rcases Cn_gen hp hP (zero_le p) with ⟨m, h⟩ | ⟨w, hw, hΛ, hlt, h⟩ |
          ⟨m, x, hx, _, hcx, hX, h⟩ | ⟨π, β, hπ, hβ, _, _, hψ, hn, h⟩
      · cases m with
        | zero => exact absurd h hP.1
        | succ m => exact ⟨.M (m + 1), ⟨Good.M _ (Nat.succ_le_succ (Nat.zero_le m)), rfl⟩, h.symm⟩
      · obtain ⟨tw, gw, ew⟩ := ihb w hw
        subst ew
        have hf : omegaFixed tw = false := by
          cases hof : omegaFixed tw with
          | false => rfl
          | true => rw [gw.inv.fixed hof] at hlt; exact absurd hlt (lt_irrefl _)
        exact ⟨.Om tw, ⟨Good.om tw gw hf, rfl⟩, h.symm⟩
      · obtain ⟨tx, gx, ex⟩ := ihb x hx
        subst ex
        have hm1 := Xi_level hX
        have hxC : C (val.{u} tx) (K m) (val tx) :=
          C_mono_base (Or.inl hX) (xiGood_of_lt hX).self
        exact ⟨.Xi m tx, ⟨Good.xi m tx hm1 gx hcx hxC, rfl⟩, h.symm⟩
      · obtain ⟨tπ, gπ, eπ⟩ := ihb π hπ
        obtain ⟨tβ, gβ, eβ⟩ := ihb β hβ
        subst eπ eβ
        have hRT := regTarget_of_Psi_lt hψ
        have hreg := isRegTerm_of_good gπ hRT
        have hact : ∀ m d, tπ = .Xi m d → val.{u} d < val tβ := by
          intro m d e
          subst e
          apply lt_of_not_le
          intro hle
          have hX := gπ.inv.xi m d rfl
          rw [show val.{u} (Tm.Xi m d) = Xi m (val d) from rfl, Psi_Xi_eq_of_le hX.1 hX.2 hle] at hψ
          exact lt_irrefl _ hψ
        exact ⟨.Psi tπ tβ, ⟨Good.psi tπ tβ gπ gβ hreg hact hn, rfl⟩, h.symm⟩
    intro z hz
    obtain ⟨l, hl⟩ := cnf_exists z
    obtain ⟨ts, hts, e⟩ := exists_terms (Q := fun t => Good.{u} t ∧ isPrincipal t = true) l
      (fun p hp => hprin p (Cn_cnf hz hl p hp) (hl.principal hp))
    have hn : Nonincr (ts.map val.{u}) := by rw [e]; exact hl.2.1
    obtain ⟨g, ev⟩ := good_ofSummands ts hts hn
    exact ⟨_, g, by rw [ev, e, ← hl.eq]⟩

/-! ### 等号の定理 -/

/-- 等号の定理：`x` が標準形の値 ⟺ `x ∈ C(Λ, 0)` -/
theorem nfValue_iff_C (x : Ordinal.{u}) :
    (∃ t, isNF t = true ∧ val.{u} t = x) ↔ C Λ 0 x := by
  constructor
  · rintro ⟨t, ht, rfl⟩
    exact C_of_good (good_of_isNF t ht)
  · intro hx
    obtain ⟨n, hn⟩ := hx
    obtain ⟨t, g, e⟩ := exists_good_of_Cn n x hn
    exact ⟨t, isNF_of_good t g, e⟩

/-! ### 整礎性と全順序 -/

/-- 標準形の項の型 -/
abbrev NF : Type := {t : Tm // isNF t = true}

/-- 標準形の上の順序 -/
def NFLt (a b : NF) : Prop := MahloOCF.lt a.1 b.1 = true

theorem wellFounded_lt_of_setting : WellFounded NFLt :=
  Subrelation.wf (r := InvImage (· < ·) (fun t : NF => val.{u} t.1))
    (fun {a b} h => (lt_iff_val.{u} a.2 b.2).mp h) (InvImage.wf _ lt_wellFounded)

end

/-! ### 弱 Mahlo 基数の列から -/

set_option warn.classDefReducibility false in
/-- 弱 Mahlo 基数の列（`h` の `n` 番目が `M_{n+1}`）からの `Setting` -/
noncomputable def settingOfMahlo
    (h : ∀ n : Nat, EnumDef.{u} WeaklyMahlo.{u} (ordNat.{u} n)) : Setting.{u} where
  Kseq := fun n => enum WeaklyMahlo (ordNat n)
  Kseq_mahlo := fun n => (h n).mem
  Kseq_lt := fun n => (h (n + 1)).lt (ordNat_lt (Nat.lt_succ_self n))

/-- 弱 Mahlo 基数の列があれば、標準形の上の順序は整礎 -/
theorem wellFounded_lt (h : ∀ n : Nat, EnumDef.{u} WeaklyMahlo.{u} (ordNat.{u} n)) :
    WellFounded NFLt := by
  letI := settingOfMahlo h
  exact wellFounded_lt_of_setting.{u}

/-- 弱 Mahlo 基数の列があれば、標準形の上の `lt` は狭義全順序 -/
theorem lt_strictTotal (h : ∀ n : Nat, EnumDef.{u} WeaklyMahlo.{u} (ordNat.{u} n)) :
    (∀ a : NF, ¬ NFLt a a) ∧ (∀ a b c : NF, NFLt a b → NFLt b c → NFLt a c) ∧
      (∀ a b : NF, NFLt a b ∨ a = b ∨ NFLt b a) := by
  letI := settingOfMahlo h
  refine ⟨?_, ?_, ?_⟩
  · intro a hlt
    exact lt_irrefl _ ((lt_iff_val.{u} a.2 a.2).mp hlt)
  · intro a b c hab hbc
    exact (lt_iff_val.{u} a.2 c.2).mpr
      (lt_trans _ _ _ ((lt_iff_val.{u} a.2 b.2).mp hab) ((lt_iff_val.{u} b.2 c.2).mp hbc))
  · intro a b
    rcases lt_total (val.{u} a.1) (val b.1) with h' | h' | h'
    · exact Or.inl ((lt_iff_val.{u} a.2 b.2).mpr h')
    · exact Or.inr (Or.inl (Subtype.ext (val_inj_of_isNF.{u} a.2 b.2 h')))
    · exact Or.inr (Or.inr ((lt_iff_val.{u} b.2 a.2).mpr h'))

/-- 弱 Mahlo 基数の列があれば、標準形の上で `cmp a b = .eq ↔ a = b` -/
theorem cmp_eq_iff (h : ∀ n : Nat, EnumDef.{u} WeaklyMahlo.{u} (ordNat.{u} n)) (a b : NF) :
    cmp a.1 b.1 = .eq ↔ a = b := by
  letI := settingOfMahlo h
  constructor
  · intro e
    exact Subtype.ext (eq_of_cmp_eq.{u} a.2 b.2 e)
  · intro e
    rw [e]
    exact (cmp_eq_iff_val.{u} b.2 b.2).mpr rfl

end OCF.Mahlo
