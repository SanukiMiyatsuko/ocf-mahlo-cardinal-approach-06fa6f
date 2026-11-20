import Mahlo.FS.PsiMul

/-! 極限 `X` の崩壊 `Ψ_π(X)` の近似 `Ψ_π(pre ⊕ A')`（`X = pre + R`、`A' < R`）のための補題。

* 和の分解（`lt_split`）：`Y < pre + R` なら `Y ≤ pre` か `Y = pre ⊕ y'`（`0 < y' < R`）。
* 引数の条件（`argCond`）：`X` の加数の真の部分項 `Y` が `Y < X` なら `Y < pre ⊕ A'`。
  `A'` が `R` の真の部分項（`R` 未満のもの）を越えていること（隙間）から出る。和の末尾は部分項
  （`tail_mem_subs`）なので、`Y = pre ⊕ y'` の `y'` は `R` の部分項になる。
* 崩壊の共終性（`cof_psi_gen`）：引数の族 `A i` が有向で `X` 未満の標準形を越えるなら、`Ψ_π(X)` 未満の
  標準形はどれかの `Ψ_π(A i)` 未満。`x` の部分項に現れる `Ψ_π(Y)` は有限個なので、それらの `Y` を全て越える
  `A i` を取って移し替え（`below_transfer`）を使う。 -/

namespace MahloOCF.FS

open Tm

/-! ### 並び -/

/-- 標準形の並び `pre ++ S` では、`pre` の元は `S` の元以上 -/
theorem nfl_append_ge {pre S : List Tm} (h : NFL (pre ++ S)) :
    ∀ a, a ∈ pre → ∀ b, b ∈ S → cmp b a ≠ .gt := by
  intro a ha b hb
  obtain ⟨L1, L2, e⟩ := List.append_of_mem ha
  rw [e, List.append_assoc] at h
  have h2 : NFL (a :: (L2 ++ S)) := nfl_append_right h
  exact le_head_of_nfl h2 b (List.mem_append_right _ hb)

/-- 吸収のない和：`pre ++ S` が標準形の並びなら `pre ⊕ S` の加数は `pre ++ S` -/
theorem summands_oadd_nfl {pre S : List Tm} (h : NFL (pre ++ S)) :
    summands (oadd (ofSummands pre) (ofSummands S)) = pre ++ S := by
  have hpre : NFL pre := nfl_append_left h
  have hS : NFL S := nfl_append_right h
  have hsp := summands_ofSummands pre (nfl_principal hpre)
  cases S with
  | nil =>
    show summands (ofSummands pre) = pre ++ []
    rw [hsp, List.append_nil]
  | cons h' r =>
    have hsS := summands_ofSummands (h' :: r) (nfl_principal hS)
    rw [summands_oadd hsS (by rw [hsp]; exact nfl_principal hpre)
      (by rw [hsS]; exact nfl_principal hS), hsp, hsS]
    have hall : ∀ a, a ∈ pre → (fun s => leB h' s) a = true := fun a ha =>
      leB_iff.mpr (nfl_append_ge h a ha h' List.mem_cons_self)
    have := takeWhile_append_of_all (p := fun s => leB h' s) (A := pre) [] hall
    simp only [List.append_nil, List.takeWhile_nil] at this
    rw [this]

/-- 並びの先頭部分は全体以下 -/
theorem cmpList_take_ne_gt (l : List Tm) (k : Nat) : cmpList (l.take k) l ≠ .gt := by
  have e := (List.take_append_drop k l).symm
  cases hd : l.drop k with
  | nil =>
    rw [hd, List.append_nil] at e
    rw [← e, cmpList_self _ (fun x _ => cmpP_self x)]
    decide
  | cons a rest =>
    have := cmpList_append_lt (l.take k) (l.drop k) (by rw [hd]; simp)
    rw [← e] at this
    rw [this]
    decide

/-- 並びの比較の分解：`l < pre ++ [R]` なら、`l ≤ pre` か、`l = pre ++ L'`（`L' ≠ []`、`L' < [R]`） -/
theorem cmpList_lt_append_split : ∀ (pre l : List Tm) (R : Tm),
    (∀ x, x ∈ pre → WNF x ∧ isPrincipal x = true) → (∀ x, x ∈ l → WNF x ∧ isPrincipal x = true) →
    cmpList l (pre ++ [R]) = .lt →
    cmpList l pre ≠ .gt ∨ ∃ L', l = pre ++ L' ∧ L' ≠ [] ∧ cmpList L' [R] = .lt
  | [], [], _, _, _, _ => Or.inl (by rw [cmpList_nil_nil]; decide)
  | [], y :: l', _, _, _, h => Or.inr ⟨y :: l', rfl, by simp, h⟩
  | a :: pre', [], _, _, _, _ => Or.inl (by rw [cmpList_nil_cons]; decide)
  | a :: pre', y :: l', R, hp, hl, h => by
    have h' : cmpList (y :: l') (a :: (pre' ++ [R])) = .lt := h
    cases e : cmpP y a with
    | lt => exact Or.inl (by rw [cmpList_head_lt _ _ e]; decide)
    | gt =>
      rw [cmpList_cons_cons_ne _ _ (by rw [e]; decide), e] at h'
      cases h'
    | eq =>
      have hya : y = a := eq_of_cmpP_eqY (hl y List.mem_cons_self).1 (hp a List.mem_cons_self).1
        (hl y List.mem_cons_self).2 (hp a List.mem_cons_self).2 e
      subst hya
      rw [cmpList_cons_cons_eq _ _ e] at h'
      rcases cmpList_lt_append_split pre' l' R (fun x hx => hp x (List.mem_cons_of_mem _ hx))
          (fun x hx => hl x (List.mem_cons_of_mem _ hx)) h' with h1 | ⟨L', e1, e2, e3⟩
      · exact Or.inl (by rw [cmpList_cons_cons_eq _ _ e]; exact h1)
      · exact Or.inr ⟨L', by rw [e1]; rfl, e2, e3⟩

/-! ### 和の分解 -/

/-- `X` の加数が `pre ++ [R]` なら `X = pre ⊕ R` -/
theorem eq_oadd_of_summands {X R : Tm} {pre : List Tm} (hX : WNF X) (hsX : summands X = pre ++ [R]) :
    X = oadd (ofSummands pre) R := by
  have hXn : NFL (pre ++ [R]) := by rw [← hsX]; exact nfl_summands hX
  have hR := hXn.1 R (by simp)
  have h1 := summands_oadd_nfl hXn
  rw [show ofSummands [R] = R from rfl] at h1
  exact eq_of_summands_eq hX (wnf_oadd (wnf_ofSummands (nfl_append_left hXn)) hR.1)
    (by rw [h1]; exact hsX)

/-- `Y < X`（`X` の加数は `pre ++ [R]`）なら、`Y ≤ pre` か、`Y = pre ⊕ y'`（`0 < y' < R`） -/
theorem lt_split {X Y R : Tm} {pre : List Tm} (hX : WNF X) (hsX : summands X = pre ++ [R])
    (hY : WNF Y) (h : Lt Y X) :
    Le Y (ofSummands pre) ∨ ∃ y', WNF y' ∧ y' ≠ .zero ∧ Lt y' R ∧
      summands Y = pre ++ summands y' ∧ Y = oadd (ofSummands pre) y' := by
  have hXn : NFL (pre ++ [R]) := by rw [← hsX]; exact nfl_summands hX
  have hpre : NFL pre := nfl_append_left hXn
  have hYn := nfl_summands hY
  have hR := hXn.1 R (by simp)
  have h' : cmpList (summands Y) (pre ++ [R]) = .lt := by
    have := h; unfold Lt at this; rw [cmp_eq, hsX] at this; exact this
  rcases cmpList_lt_append_split pre (summands Y) R hpre.1 hYn.1 h' with h1 | ⟨L', e1, e2, e3⟩
  · left
    refine le_of_ne_gtY hY (wnf_ofSummands hpre) ?_
    rw [cmp_eq, summands_ofSummands pre (nfl_principal hpre)]
    exact h1
  · right
    have hn : NFL (pre ++ L') := by rw [← e1]; exact hYn
    have hL' : NFL L' := nfl_append_right hn
    have hsL := summands_ofSummands L' (nfl_principal hL')
    refine ⟨ofSummands L', wnf_ofSummands hL', ofSummands_ne_zero e2 (nfl_principal hL'), ?_, ?_, ?_⟩
    · unfold Lt
      rw [cmp_eq, hsL, summands_principal hR.2]
      exact e3
    · rw [hsL]; exact e1
    · exact eq_of_summands_eq hY (wnf_oadd (wnf_ofSummands hpre) (wnf_ofSummands hL'))
        (by rw [summands_oadd_nfl hn]; exact e1)

theorem eq_nil_of_singleton_eq {a b : Tm} {L S : List Tm} (h : [b] = a :: L ++ S) : S = [] := by
  have h2 := congrArg List.length h
  simp only [List.length_cons, List.length_nil, List.length_append] at h2
  exact List.eq_nil_of_length_eq_zero (by omega)

/-- 和の末尾は部分項 -/
theorem tail_mem_subs : ∀ (L : List Tm) {Y y' : Tm}, WNF Y → WNF y' → y' ≠ .zero →
    summands Y = L ++ summands y' → y' ∈ subs Y
  | [], Y, y', hY, hy, _, h => by
    rw [List.nil_append] at h
    rw [eq_of_summands_eq hY hy h]; exact self_mem_subs _
  | a :: L', Y, y', hY, hy, hy0, h => by
    cases Y with
    | plus a' b =>
      rw [summands_plus, List.cons_append, List.cons.injEq] at h
      exact subs_plus_r (tail_mem_subs L' hY.plus.2.1 hy hy0 h.2)
    | zero => simp [summands] at h
    | M n => exact absurd (eq_zero_of_summands_nil (eq_nil_of_singleton_eq h)) hy0
    | Om e => exact absurd (eq_zero_of_summands_nil (eq_nil_of_singleton_eq h)) hy0
    | Xi n e => exact absurd (eq_zero_of_summands_nil (eq_nil_of_singleton_eq h)) hy0
    | Psi p e => exact absurd (eq_zero_of_summands_nil (eq_nil_of_singleton_eq h)) hy0

/-- `x ⊕ y = 0` なら `x = y = 0` -/
theorem oadd_eq_zero {x y : Tm} (hx : WNF x) (hy : WNF y) (h : oadd x y = .zero) :
    x = .zero ∧ y = .zero := by
  have h1 := le_oadd_right hx hy
  have h2 := le_oadd_leftW hx hy
  rw [h] at h1 h2
  constructor
  · rcases h2 with e | e
    · exact e
    · exact absurd e (not_lt_zero _)
  · rcases h1 with e | e
    · exact e
    · exact absurd e (not_lt_zero _)

/-! ### 引数の条件 -/

/-- 引数の条件：`X = pre + R` の加数 `s` の真の部分項 `Y` が `Y < X` なら `Y < pre ⊕ A'`。
    `A'` は `R` 未満で、`R` の真の部分項のうち `R` 未満のものを越えている（隙間）。`A' = 0` のときは
    `R` に真の部分項がないとする -/
theorem argCond {X R A' : Tm} {pre : List Tm} (hX : WNF X) (hsX : summands X = pre ++ [R])
    (hA : WNF A') (hgap : ∀ v, v ∈ subs R → v ≠ R → Lt v R → Lt v A')
    (hpos : A' = .zero → ∀ v, v ∈ subs R → v = R) :
    ∀ s, s ∈ summands X → ∀ Y, Y ∈ subs s → Y ≠ s → Lt Y X →
      Lt Y (oadd (ofSummands pre) A') := by
  intro s hs Y hYs hYne hYX
  have hXn : NFL (pre ++ [R]) := by rw [← hsX]; exact nfl_summands hX
  have hpre : NFL pre := nfl_append_left hXn
  have hPF := wnf_ofSummands hpre
  have hsF := (summands_WNF X hX s hs).1
  have hYF := hsF.of_mem_subs hYs
  rw [hsX] at hs
  rcases lt_split hX hsX hYF hYX with hle | ⟨y', hy', hy'0, hy'R, hsY, hYe⟩
  · by_cases hA0 : A' = .zero
    · -- `A' = 0`：`Y ≠ pre` を示す
      rw [hA0]
      show Lt Y (ofSummands pre)
      rcases hle with e | hlt
      · exfalso
        rcases List.mem_append.mp hs with hs1 | hs1
        · have hsP : s ∈ subs Y := by
            rw [e]
            exact mem_subs_of_mem_summands
              (by rw [summands_ofSummands pre (nfl_principal hpre)]; exact hs1)
          exact hYne (eq_of_mem_subs_size hYs (size_le_of_mem_subs hsP))
        · rw [List.mem_singleton.mp hs1] at hYs hYne
          exact hYne (hpos hA0 Y hYs)
      · exact hlt
    · exact lt_of_le_of_ltY hYF hPF (wnf_oadd hPF hA) hle (lt_oadd_left hPF hA hA0)
  · -- `Y = pre ⊕ y'`：`s = R` で、`y'` は `R` の部分項
    have hy'Y : y' ∈ subs Y := tail_mem_subs pre hYF hy' hy'0 hsY
    have hsR : s = R := by
      rcases List.mem_append.mp hs with hs1 | hs1
      · exfalso
        have hsY' : s ∈ subs Y :=
          mem_subs_of_mem_summands (by rw [hsY]; exact List.mem_append_left _ hs1)
        exact hYne (eq_of_mem_subs_size hYs (size_le_of_mem_subs hsY'))
      · exact List.mem_singleton.mp hs1
    rw [hsR] at hYs
    have hy'A : Lt y' A' := hgap y' (subs_trans hYs hy'Y) (Lt.ne hy'R) hy'R
    rw [hYe]
    exact oadd_lt_oadd hPF hy' hA hy'A

/-- `X` の部分項 `Ψ_π(Y)` の引数 `Y` は、`X` のどれかの加数の真の部分項 -/
theorem psi_arg_in_summand {X π Y : Tm} (h : Tm.Psi π Y ∈ subs X) :
    ∃ s, s ∈ summands X ∧ Y ∈ subs s ∧ Y ≠ s := by
  have hsz : ∀ s, Tm.Psi π Y ∈ subs s → Y ≠ s := fun s hs => by
    have := size_le_of_mem_subs hs
    exact ne_of_size_lt (by simp only [Tm.size] at this; omega)
  rcases subs_sum_cases h with ⟨L, hL⟩ | ⟨s, hs, hv⟩
  · have hmem : Tm.Psi π Y ∈ summands X := by
      rw [hL]; exact List.mem_append_right _ (by simp [summands])
    exact ⟨_, hmem, mem_subs_psi_a π Y, hsz _ (self_mem_subs _)⟩
  · exact ⟨s, hs, subs_trans hv (mem_subs_psi_a π Y), hsz s hv⟩

/-! ### 崩壊の共終性 -/

/-- 崩壊の共終性：引数の族 `A i` が有向で `X` 未満の標準形を越えるなら、`Ψ_π(X)` 未満の標準形は
    どれかの `Ψ_π(A i)` 未満 -/
theorem cof_psi_gen {π X : Tm} (hπ : WNF π) (hT : IsTgt π) {ι : Type} (A : ι → Tm) (i0 : ι)
    (hdir : ∀ i j, ∃ k, (∀ Y, WNF Y → Lt Y (A i) → Lt Y (A k)) ∧
      (∀ Y, WNF Y → Lt Y (A j) → Lt Y (A k)))
    (hcof : ∀ Y, WNF Y → Lt Y X → ∃ i, Lt Y (A i)) :
    ∀ x, WNF x → Lt x (.Psi π X) → ∃ i, Lt x (.Psi π (A i)) := by
  have key : ∀ l : List Tm, (∀ v, v ∈ l → WNF v) →
      ∃ i, ∀ Y, Tm.Psi π Y ∈ l → Lt Y X → Lt Y (A i) := by
    intro l
    induction l with
    | nil => intro _; exact ⟨i0, fun Y h => by cases h⟩
    | cons v l ih =>
      intro hl
      obtain ⟨i, hi⟩ := ih (fun w hw => hl w (List.mem_cons_of_mem _ hw))
      have hrest : (∀ Y, v = Tm.Psi π Y → Lt Y X → False) →
          ∃ i, ∀ Y, Tm.Psi π Y ∈ v :: l → Lt Y X → Lt Y (A i) := by
        intro hno
        refine ⟨i, fun Y hY hYX => ?_⟩
        rcases List.mem_cons.mp hY with e | hY
        · exact absurd hYX (fun h => hno Y e.symm h)
        · exact hi Y hY hYX
      cases v with
      | Psi κ Y0 =>
        by_cases hκ : κ = π
        · by_cases hlt : Lt Y0 X
          · subst hκ
            have hY0F : WNF Y0 := (hl _ List.mem_cons_self).psi.aF
            obtain ⟨j, hj⟩ := hcof Y0 hY0F hlt
            obtain ⟨k, hk1, hk2⟩ := hdir i j
            refine ⟨k, fun Y hY hYX => ?_⟩
            rcases List.mem_cons.mp hY with e | hY
            · cases e
              exact hk2 Y0 hY0F hj
            · have hYF : WNF Y := (hl _ (List.mem_cons_of_mem _ hY)).psi.aF
              exact hk1 Y hYF (hi Y hY hYX)
          · exact hrest (fun Y e h => by cases e; exact hlt h)
        · exact hrest (fun Y e _ => by cases e; exact hκ rfl)
      | zero => exact hrest (fun Y e _ => by cases e)
      | M n => exact hrest (fun Y e _ => by cases e)
      | plus a b => exact hrest (fun Y e _ => by cases e)
      | Om a => exact hrest (fun Y e _ => by cases e)
      | Xi n a => exact hrest (fun Y e _ => by cases e)
  intro x hx hlt
  obtain ⟨i, hi⟩ := key (subs x) (fun v hv => hx.of_mem_subs hv)
  exact ⟨i, below_transfer hπ hT x hx (fun Y hYs hYX => hi Y hYs hYX) hlt⟩

/-! ### 和の後ろの部分 -/

/-- 加数の後ろの部分（`0` でない）の `lfr` は全体の `lfr` の元以下 -/
theorem lfr_suffix {σ : Tm} (hσ : WNF σ) :
    ∀ (pre : List Tm) {a a' f : Tm}, WNF a → WNF a' → a' ≠ .zero →
      summands a = pre ++ summands a' → f ∈ lfr σ a' → ∃ g, g ∈ lfr σ a ∧ Le f g := by
  intro pre
  induction pre with
  | nil =>
    intro a a' f ha ha' _ hs hf
    have e : a = a' := by
      rw [← ofSummands_summands a ha, ← ofSummands_summands a' ha', hs, List.nil_append]
    subst e
    exact ⟨f, hf, Or.inl rfl⟩
  | cons p pre ih =>
    intro a a' f ha ha' ha'0 hs hf
    have hfF := ha'.of_mem_subs (lfr_spec hf).1
    cases a with
    | zero => simp [summands] at hs
    | plus a1 a2 =>
      obtain ⟨ha1, ha2, -, -⟩ := ha.plus
      simp only [summands, List.cons_append, List.cons.injEq] at hs
      by_cases haσ : Lt (.plus a1 a2) σ
      · refine ⟨_, by rw [lfr_of_lt haσ]; exact List.mem_singleton.mpr rfl, ?_⟩
        have ha'a : Le a' (.plus a1 a2) := by
          refine le_of_tail (L := p :: pre) ha ha' ?_
          simp only [summands, hs.1, hs.2, List.cons_append]
        exact le_transY hfF ha' ha (lfr_le hσ ha' hf) ha'a
      · obtain ⟨g, hg, hfg⟩ := ih ha2 ha' ha'0 hs.2 hf
        exact ⟨g, (mem_lfr_plus haσ).mpr (Or.inr hg), hfg⟩
    | _ =>
      simp only [summands, List.cons_append, List.cons.injEq] at hs
      have hp : pre ++ summands a' = [] := hs.2.symm
      simp only [List.append_eq_nil_iff] at hp
      exact absurd (eq_zero_of_summands_nil hp.2) ha'0

end MahloOCF.FS
