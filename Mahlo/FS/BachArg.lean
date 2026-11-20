import Mahlo.FS.BachMul

/-! 和の区間の分け方（`gen_split`）：並び `Q` の後ろに `x ≤ y` を足した `Q ⊕ x < B ≤ Q ⊕ y`（`B` は後者でない）なら、
`Q ⊕ x ≤ B[0]` か、`B` は `Q` の先頭部分 `Q₁` の後ろに主要項 `b`（`Q` の続きより大きい、`x < b ≤ y`）を足したもの。
`LBI x y` を仮定する。崩壊の持ち上げで、有効性の調整 `rt + 1` を前に置いた近似の区間に使う。 -/

namespace MahloOCF.FS

open Tm

/-! ### 並びの後ろに足す -/

/-- 先頭 `q` が残る：`(q :: Q') ⊕ z` の加数は `q :: (Q' ⊕ z)` の加数 -/
theorem summands_oadd_cons_keep {q : Tm} {Q' : List Tm} {z : Tm} (hQ : NFL (q :: Q')) (hz : WNF z)
    (hk : ∀ h r, summands z = h :: r → leB h q = true) :
    summands (oadd (ofSummands (q :: Q')) z) = q :: summands (oadd (ofSummands Q') z) := by
  have hQ' : NFL Q' := nfl_tail hQ
  have hsQ := summands_ofSummands (q :: Q') (nfl_principal hQ)
  have hsQ' := summands_ofSummands Q' (nfl_principal hQ')
  cases hs : summands z with
  | nil =>
    rw [eq_zero_of_summands_nil hs, oadd_zero, oadd_zero, hsQ, hsQ']
  | cons h r =>
    have hzp : ∀ s, s ∈ summands z → isPrincipal s = true := fun s hs' => (summands_WNF z hz s hs').2
    rw [summands_oadd hs (by rw [hsQ]; exact nfl_principal hQ) hzp,
      summands_oadd hs (by rw [hsQ']; exact nfl_principal hQ') hzp, hsQ, hsQ',
      List.takeWhile_cons_of_pos (by simp [hk h r hs])]
    rfl

/-- 先頭 `q` より大きい `z` は全部を吸収する -/
theorem oadd_cons_absorb {q : Tm} {Q' : List Tm} {z h : Tm} {r : List Tm} (hQ : NFL (q :: Q'))
    (hz : WNF z) (hs : summands z = h :: r) (hnk : leB h q = false) :
    oadd (ofSummands (q :: Q')) z = z := by
  have hsQ := summands_ofSummands (q :: Q') (nfl_principal hQ)
  rw [oadd_eq_ofSummands (wnf_ofSummands hQ) hz hs, hsQ,
    List.takeWhile_cons_of_neg (by simp [hnk]), List.nil_append]
  exact ofSummands_summands z hz

/-! ### 同じ先頭の比較 -/

theorem lt_cons_iff {T U q : Tm} {L M : List Tm} (hT : summands T = q :: L) (hU : summands U = q :: M) :
    Lt T U ↔ cmpList L M = .lt := by
  unfold Lt
  rw [cmp_eq, hT, hU, cmpList_cons_cons_eq _ _ (cmpP_self q)]

theorem tail_spec {B q : Tm} {rB : List Tm} (hB : WNF B) (hs : summands B = q :: rB) :
    WNF (ofSummands rB) ∧ summands (ofSummands rB) = rB := by
  have hn := nfl_summands hB
  rw [hs] at hn
  have ht := nfl_tail hn
  exact ⟨wnf_ofSummands ht, summands_ofSummands rB (nfl_principal ht)⟩

theorem eq_plus_of_summands {B q : Tm} {rB : List Tm} (hB : WNF B) (hs : summands B = q :: rB)
    (hr : rB ≠ []) : B = .plus q (ofSummands rB) := by
  have e := ofSummands_summands B hB
  rw [hs] at e
  rw [← e]
  cases rB with
  | nil => exact absurd rfl hr
  | cons a l => rfl

/-- `x ≤ y` なら先頭の加数も `≤` -/
theorem head_le_of_le {x y hx hy : Tm} {rx ry : List Tm} (hxs : summands x = hx :: rx)
    (hys : summands y = hy :: ry) (h : Le x y) : cmpP hx hy ≠ .gt := by
  rcases h with rfl | h
  · rw [hxs] at hys; cases hys; rw [cmpP_self]; decide
  · exact head_le_of_lt hxs hys h

/-- 主要項 `b` より小さい加数だけの和は `b` 未満 -/
theorem lt_prin_of_summands_le {x b q : Tm} (hx : WNF x) (hbp : isPrincipal b = true) (hqb : Lt q b)
    (hqF : WNF q) (hbF : WNF b) (h : ∀ s, s ∈ summands x → Le s q) : Lt x b :=
  lt_of_summands_lt hx hbp (fun u hu =>
    lt_of_le_of_ltY (summands_WNF x hx u hu).1 hqF hbF (h u hu) hqb)

/-- 同じ先頭の後ろの比較 `≤` を先頭つきに移す -/
theorem le_cons_of_le {T U q L M : Tm} (hT : WNF T) (hU : WNF U) (_hL : WNF L) (_hM : WNF M)
    (hTs : summands T = q :: summands L) (hUs : summands U = q :: summands M) (h : Le L M) : Le T U := by
  rcases h with rfl | h
  · left; exact eq_of_summands_eq hT hU (by rw [hTs, hUs])
  · right
    refine (lt_cons_iff hTs hUs).mpr ?_
    have := h; unfold Lt at this; rwa [cmp_eq] at this

theorem le_of_le_cons {T U q L M : Tm} (_hT : WNF T) (_hU : WNF U) (hL : WNF L) (hM : WNF M)
    (hTs : summands T = q :: summands L) (hUs : summands U = q :: summands M) (h : Le T U) : Le L M := by
  rcases h with rfl | h
  · left
    have e := hTs.symm.trans hUs
    simp only [List.cons.injEq, true_and] at e
    exact eq_of_summands_eq hL hM e
  · right
    have := (lt_cons_iff hTs hUs).mp h
    unfold Lt; rwa [cmp_eq]

theorem lt_of_lt_cons {T U q L M : Tm} (hTs : summands T = q :: summands L)
    (hUs : summands U = q :: summands M) (h : Lt T U) : Lt L M := by
  have := (lt_cons_iff hTs hUs).mp h
  unfold Lt; rwa [cmp_eq]

/-- `q ⊕ w`（`w` の先頭は `q` 以下）の加数 -/
theorem summands_oadd_prin_keep {q w : Tm} (hqF : WNF q) (hqp : isPrincipal q = true) (hw : WNF w)
    (hk : ∀ h r, summands w = h :: r → leB h q = true) : summands (oadd q w) = q :: summands w := by
  have hQ : NFL [q] := ⟨fun s hs => by simp at hs; subst hs; exact ⟨hqF, hqp⟩, trivial⟩
  have := summands_oadd_cons_keep hQ hw hk
  have e1 : ofSummands [q] = q := rfl
  rw [e1] at this
  rw [this]
  show q :: summands (oadd .zero w) = q :: summands w
  rw [zero_oadd hw]

/-- 先頭の加数の比較から大小 -/
theorem lt_of_heads {T U a b : Tm} {L M : List Tm} (hT : summands T = a :: L) (hU : summands U = b :: M)
    (e : cmpP a b = .lt) : Lt T U := by
  unfold Lt
  rw [cmp_eq, hT, hU, cmpList_cons_cons_ne _ _ (by rw [e]; decide), e]

theorem cmpP_swap_gt {a b : Tm} (ha : WNF a) (hb : WNF b) (hap : isPrincipal a = true)
    (hbp : isPrincipal b = true) (e : cmpP a b = .gt) : cmpP b a = .lt := by
  have h := swapY ha hb
  rw [cmp_principal hbp hap, cmp_principal hap hbp, e] at h
  exact h

/-- 和の区間の分け方 -/
theorem gen_split : ∀ (Q : List Tm), NFL Q → ∀ {x y B : Tm}, WNF x → WNF y → WNF B →
    ¬ isSucc B = true → Le x y → LBI x y →
    Lt (oadd (ofSummands Q) x) B → Le B (oadd (ofSummands Q) y) →
    Le (oadd (ofSummands Q) x) (fund B .zero) ∨
    ∃ Q₁ Q₂ b, Q = Q₁ ++ Q₂ ∧ Q₂ ≠ [] ∧ summands B = Q₁ ++ [b] ∧ isPrincipal b = true ∧
      (∀ q, Q₂.head? = some q → Lt q b) ∧ Lt x b ∧ Le b y
  | [], _, x, y, B, hx, hy, hB, _, _, hL, h1, h2 => by
    have e0 : ofSummands ([] : List Tm) = .zero := rfl
    rw [e0, zero_oadd hx] at h1 ⊢
    rw [e0, zero_oadd hy] at h2
    exact Or.inl (hL B hB h1 h2)
  | q :: Q', hQ, x, y, B, hx, hy, hB, hns, hxy, hL, h1, h2 => by
    have hqF := (hQ.1 q List.mem_cons_self).1
    have hqp := (hQ.1 q List.mem_cons_self).2
    have hQ' : NFL Q' := nfl_tail hQ
    have hQF := wnf_ofSummands hQ
    have hQ'F := wnf_ofSummands hQ'
    have hSx := wnf_oadd hQF hx
    have hSy := wnf_oadd hQF hy
    have hS'x := wnf_oadd hQ'F hx
    have hS'y := wnf_oadd hQ'F hy
    have hQ'le : ∀ s, s ∈ Q' → Le s q := fun s hs =>
      le_of_ne_gtY (hQ.1 s (List.mem_cons_of_mem _ hs)).1 hqF (le_head_of_nfl hQ s hs)
    have hB0 : B ≠ .zero := fun e => by rw [e] at h1; exact not_lt_zero _ h1
    obtain ⟨b0, rB, hBs⟩ := List.exists_cons_of_ne_nil (summands_ne_nil hB0)
    have hb0F := (summands_WNF B hB b0 (by rw [hBs]; exact List.mem_cons_self)).1
    have hb0p := (summands_WNF B hB b0 (by rw [hBs]; exact List.mem_cons_self)).2
    obtain ⟨hB'F, hB's⟩ := tail_spec hB hBs
    -- 先頭の加数が `q` に等しい場合：後ろで帰納法
    have hrec : b0 = q → Lt (oadd (ofSummands Q') x) (ofSummands rB) →
        Le (ofSummands rB) (oadd (ofSummands Q') y) →
        summands (oadd (ofSummands (q :: Q')) x) = q :: summands (oadd (ofSummands Q') x) →
        Le (oadd (ofSummands (q :: Q')) x) (fund B .zero) ∨
        ∃ Q₁ Q₂ b, q :: Q' = Q₁ ++ Q₂ ∧ Q₂ ≠ [] ∧ summands B = Q₁ ++ [b] ∧ isPrincipal b = true ∧
          (∀ q', Q₂.head? = some q' → Lt q' b) ∧ Lt x b ∧ Le b y := by
      intro hb0q h1' h2' hSxs
      subst hb0q
      have hrB : rB ≠ [] := by
        intro e
        rw [e] at h1'
        exact not_lt_zero _ h1'
      have hBe := eq_plus_of_summands hB hBs hrB
      have hns' : ¬ isSucc (ofSummands rB) = true := by
        rw [hBe, isSucc_plus (ofSummands_ne_zero hrB (nfl_principal (nfl_tail (by
          have := nfl_summands hB; rwa [hBs] at this))))] at hns
        exact hns
      rcases gen_split Q' hQ' hx hy hB'F hns' hxy hL h1' h2' with hA | ⟨Q₁, Q₂, b, e1, e2, e3, e4, e5, e6, e7⟩
      · left
        have hB'0 : ofSummands rB ≠ .zero := ofSummands_ne_zero hrB (nfl_principal (nfl_tail (by
          have := nfl_summands hB; rwa [hBs] at this)))
        have hd1 : dom (ofSummands rB) ≠ .one := fun e => hns' ((dom_eq_one_iff hB'F).mp e)
        have hf0 : fund B .zero = oadd b0 (fund (ofSummands rB) .zero) := by
          rw [hBe]; exact f0_plus (by rw [← hBe]; exact hB) hd1
        have hf0F := wnf_f0 hB'F
        have hk : ∀ h r, summands (fund (ofSummands rB) .zero) = h :: r → leB h b0 = true := by
          intro h r hs
          have hlt := f0_lt hB'F hB'0
          obtain ⟨h', r', hs'⟩ := List.exists_cons_of_ne_nil (summands_ne_nil hB'0)
          have e1 := head_le_of_lt hs hs' hlt
          have hh'F := (summands_WNF _ hB'F h' (by rw [hs']; exact List.mem_cons_self)).1
          have hhF := (summands_WNF _ hf0F h (by rw [hs]; exact List.mem_cons_self)).1
          have e2 : Le h' b0 := by
            have hn := nfl_summands hB
            rw [hBs] at hn
            have hmem : h' ∈ rB := by rw [← hB's, hs']; exact List.mem_cons_self
            exact le_of_ne_gtY hh'F hb0F (le_head_of_nfl hn h' hmem)
          have hhp := (summands_WNF _ hf0F h (by rw [hs]; exact List.mem_cons_self)).2
          have hh'p := (summands_WNF _ hB'F h' (by rw [hs']; exact List.mem_cons_self)).2
          exact le_leB (le_transY hhF hh'F hb0F
            (le_of_ne_gtY hhF hh'F (by rw [cmp_principal hhp hh'p]; exact e1)) e2)
        rw [hf0]
        exact le_cons_of_le hSx (wnf_oadd hb0F hf0F) hS'x hf0F hSxs
          (summands_oadd_prin_keep hb0F hb0p hf0F hk) hA
      · right
        refine ⟨b0 :: Q₁, Q₂, b, (by rw [e1]; rfl), e2, ?_, e4, e5, e6, e7⟩
        rw [hBs, ← hB's, e3]; rfl
    -- `B` の後ろは `B` 未満
    have hBs' : summands B = b0 :: summands (ofSummands rB) := by rw [hB's]; exact hBs
    have hB'lt : Lt (ofSummands rB) B := by
      by_cases hrB : rB = []
      · have e : ofSummands rB = .zero := by rw [hrB]; rfl
        rw [e]; exact zero_lt hB0
      · have hBe := eq_plus_of_summands hB hBs hrB
        have hB2 := hB
        rw [hBe] at hB2 ⊢
        exact lt_plus_rightY hB2
    -- `y ≠ 0`
    have hy0 : y ≠ .zero := by
      intro e; subst e
      have hx0 : x = .zero := by
        rcases hxy with e | h
        · exact e
        · exact absurd h (not_lt_zero _)
      subst hx0
      exact not_lt_of_leY hB hSx h2 h1
    obtain ⟨hy0, ry, hys⟩ := List.exists_cons_of_ne_nil (summands_ne_nil hy0)
    have hy0F := (summands_WNF y hy hy0 (by rw [hys]; exact List.mem_cons_self)).1
    have hy0p := (summands_WNF y hy hy0 (by rw [hys]; exact List.mem_cons_self)).2
    -- `x` の加数は先頭以下
    have hxle : ∀ hx0 rx, summands x = hx0 :: rx → ∀ s, s ∈ summands x → Le s hx0 := by
      intro hx0 rx hxs s hs
      have hn := nfl_summands hx
      rw [hxs] at hn
      have hsF := (summands_WNF x hx s hs).1
      have hx0F := (summands_WNF x hx hx0 (by rw [hxs]; exact List.mem_cons_self)).1
      rw [hxs] at hs
      rcases List.mem_cons.mp hs with rfl | hs'
      · exact Or.inl rfl
      · exact le_of_ne_gtY hsF hx0F (le_head_of_nfl hn s hs')
    -- `S ⊕ x` が `q` を残す場合の、`B` の先頭による場合分け
    have keep_case : summands (oadd (ofSummands (q :: Q')) x) = q :: summands (oadd (ofSummands Q') x) →
        (b0 = q → Le (ofSummands rB) (oadd (ofSummands Q') y)) →
        (cmpP b0 q = .gt → Le B y) →
        (∀ s, s ∈ summands x → Le s q) →
        Le (oadd (ofSummands (q :: Q')) x) (fund B .zero) ∨
        ∃ Q₁ Q₂ b, q :: Q' = Q₁ ++ Q₂ ∧ Q₂ ≠ [] ∧ summands B = Q₁ ++ [b] ∧ isPrincipal b = true ∧
          (∀ q', Q₂.head? = some q' → Lt q' b) ∧ Lt x b ∧ Le b y := by
      intro hSxs h2' hgy hxq
      cases e : cmpP b0 q with
      | lt => exact absurd h1 (Lt.asymmY hB hSx (lt_of_heads hBs hSxs e))
      | eq =>
        have hb0q := eq_of_cmpP_eqY hb0F hqF hb0p hqp e
        subst hb0q
        exact hrec rfl (lt_of_lt_cons hSxs hBs' h1) (h2' rfl) hSxs
      | gt =>
        have hqb : Lt q b0 := by
          unfold Lt; rw [cmp_principal hqp hb0p]; exact cmpP_swap_gt hb0F hqF hb0p hqp e
        by_cases hrB : rB = []
        · -- `B = b0` は主要項
          right
          have hBb : B = b0 := by
            have := ofSummands_summands B hB
            rw [hBs, hrB] at this
            exact this.symm
          refine ⟨[], q :: Q', b0, rfl, List.cons_ne_nil _ _, by rw [hBs, hrB]; rfl, hb0p,
            fun q' hq' => ?_, lt_prin_of_summands_le hx hb0p hqb hqF hb0F hxq, ?_⟩
          · simp only [List.head?_cons, Option.some.injEq] at hq'
            subst hq'; exact hqb
          · rw [← hBb]; exact hgy e
        · -- `B` は和：`B[0] ≥ b0 > S ⊕ x`
          left
          have hBe := eq_plus_of_summands hB hBs hrB
          have hSxle : ∀ s, s ∈ summands (oadd (ofSummands (q :: Q')) x) → Le s q := by
            intro s hs
            have hn := nfl_summands hSx
            rw [hSxs] at hn hs
            have hsF := hn.1 s hs
            rcases List.mem_cons.mp hs with rfl | hs'
            · exact Or.inl rfl
            · exact le_of_ne_gtY hsF.1 hqF (le_head_of_nfl hn s hs')
          have hlt := lt_prin_of_summands_le hSx hb0p hqb hqF hb0F hSxle
          have hB2 := hB
          rw [hBe] at hB2
          have hh := head_le_f0 hB2
          rw [← hBe] at hh
          exact Or.inr (lt_of_lt_of_leY hSx hb0F (wnf_f0 hB) hlt hh)
    cases hky : leB hy0 q with
    | true =>
      -- `y` の先頭は `q` 以下：`q` は両方に残る
      have hky' : ∀ h r, summands y = h :: r → leB h q = true := fun h r hs => by
        rw [hys] at hs; cases hs; exact hky
      have hkx : ∀ h r, summands x = h :: r → leB h q = true := by
        intro h r hs
        have hhF := (summands_WNF x hx h (by rw [hs]; exact List.mem_cons_self)).1
        have hhp := (summands_WNF x hx h (by rw [hs]; exact List.mem_cons_self)).2
        have e1 := head_le_of_le hs hys hxy
        exact le_leB (le_transY hhF hy0F hqF
          (le_of_ne_gtY hhF hy0F (by rw [cmp_principal hhp hy0p]; exact e1))
          (le_of_ne_gtY hy0F hqF (leB_iff.mp hky)))
      have hSxs := summands_oadd_cons_keep hQ hx hkx
      have hSys := summands_oadd_cons_keep hQ hy hky'
      have hxq : ∀ s, s ∈ summands x → Le s q := by
        intro s hs
        obtain ⟨hx0, rx, hxs⟩ := List.exists_cons_of_ne_nil (List.ne_nil_of_mem hs)
        have hx0F := (summands_WNF x hx hx0 (by rw [hxs]; exact List.mem_cons_self)).1
        exact le_transY (summands_WNF x hx s hs).1 hx0F hqF (hxle hx0 rx hxs s hs)
          (le_of_ne_gtY hx0F hqF (leB_iff.mp (hkx hx0 rx hxs)))
      refine keep_case hSxs (fun hb => by subst hb; exact le_of_le_cons hB hSy hB'F hS'y hBs' hSys h2)
        (fun e => ?_) hxq
      exact absurd (lt_of_heads hSys hBs (cmpP_swap_gt hb0F hqF hb0p hqp e)) (not_lt_of_leY hB hSy h2)
    | false =>
      -- `y` の先頭は `q` より大きい：`S ⊕ y = y`
      have hSy_eq : oadd (ofSummands (q :: Q')) y = y := oadd_cons_absorb hQ hy hys hky
      have hS'y_eq : oadd (ofSummands Q') y = y := by
        cases hQ'e : Q' with
        | nil => exact zero_oadd hy
        | cons q' Q'' =>
          have hq'q : Le q' q := hQ'le q' (by rw [hQ'e]; exact List.mem_cons_self)
          have hQ'' : NFL (q' :: Q'') := by rw [← hQ'e]; exact hQ'
          refine oadd_cons_absorb hQ'' hy hys ?_
          cases e : leB hy0 q' with
          | false => rfl
          | true =>
            exfalso
            have hq'F := (hQ''.1 q' List.mem_cons_self).1
            have h3 := le_transY hy0F hq'F hqF (le_of_ne_gtY hy0F hq'F (leB_iff.mp e)) hq'q
            rw [le_leB h3] at hky; cases hky
      rw [hSy_eq] at h2
      cases hxs : summands x with
      | nil =>
        have hSxs := summands_oadd_cons_keep hQ hx (fun h r hs => by rw [hxs] at hs; cases hs)
        refine keep_case hSxs (fun _ => by rw [hS'y_eq]; exact Or.inr (lt_of_lt_of_leY hB'F hB hy hB'lt h2))
          (fun _ => h2) (fun s hs => by rw [hxs] at hs; cases hs)
      | cons hx0 rx =>
        cases hkx : leB hx0 q with
        | true =>
          have hkx' : ∀ h r, summands x = h :: r → leB h q = true := fun h r hs => by
            rw [hxs] at hs; cases hs; exact hkx
          have hSxs := summands_oadd_cons_keep hQ hx hkx'
          have hx0F := (summands_WNF x hx hx0 (by rw [hxs]; exact List.mem_cons_self)).1
          refine keep_case hSxs (fun _ => by rw [hS'y_eq]; exact Or.inr (lt_of_lt_of_leY hB'F hB hy hB'lt h2))
            (fun _ => h2) (fun s hs => le_transY (summands_WNF x hx s hs).1 hx0F hqF
              (hxle hx0 rx hxs s hs) (le_of_ne_gtY hx0F hqF (leB_iff.mp hkx)))
        | false =>
          -- `x` の先頭も `q` より大きい：`S ⊕ x = x`
          have hSx_eq : oadd (ofSummands (q :: Q')) x = x := oadd_cons_absorb hQ hx hxs hkx
          rw [hSx_eq] at h1 ⊢
          exact Or.inl (hL B hB h1 h2)

end MahloOCF.FS

/-! ### 並びの結合 -/

namespace MahloOCF.FS

open Tm

/-- `c` の加数と `w` の先頭が `p` 以下なら `c ⊕ w` の先頭も `p` 以下 -/
theorem head_oadd_le {c w p : Tm} (hc : WNF c) (hw : WNF w)
    (hcp : ∀ s, s ∈ summands c → leB s p = true) (hwp : ∀ h r, summands w = h :: r → leB h p = true) :
    ∀ h r, summands (oadd c w) = h :: r → leB h p = true := by
  intro h r hs
  cases hws : summands w with
  | nil =>
    rw [eq_zero_of_summands_nil hws, oadd_zero] at hs
    exact hcp h (by rw [hs]; exact List.mem_cons_self)
  | cons hw0 rw0 =>
    have hcpr : ∀ s, s ∈ summands c → isPrincipal s = true := fun s hs' => (summands_WNF c hc s hs').2
    have hwpr : ∀ s, s ∈ summands w → isPrincipal s = true := fun s hs' => (summands_WNF w hw s hs').2
    rw [summands_oadd hws hcpr hwpr] at hs
    cases ht : (summands c).takeWhile (fun s => leB hw0 s) with
    | nil =>
      rw [ht, List.nil_append, hws] at hs
      cases hs
      exact hwp _ _ hws
    | cons t tr =>
      rw [ht] at hs
      simp only [List.cons_append, List.cons.injEq] at hs
      rw [← hs.1]
      exact hcp t ((List.takeWhile_sublist _).subset (by rw [ht]; exact List.mem_cons_self))

/-- 主要項 `p` を前に：`p ⊕ (P' ⊕ w) = (p :: P') ⊕ w` -/
theorem oadd_cons_eq {p w : Tm} {P' : List Tm} (hP : NFL (p :: P')) (hw : WNF w)
    (hwp : ∀ h r, summands w = h :: r → leB h p = true) :
    oadd p (oadd (ofSummands P') w) = oadd (ofSummands (p :: P')) w := by
  have hpF := (hP.1 p List.mem_cons_self).1
  have hpp := (hP.1 p List.mem_cons_self).2
  have hP' := nfl_tail hP
  have hP'F := wnf_ofSummands hP'
  have hsP' := summands_ofSummands P' (nfl_principal hP')
  have hP'le : ∀ s, s ∈ summands (ofSummands P') → leB s p = true := by
    intro s hs
    rw [hsP'] at hs
    exact leB_iff.mpr (le_head_of_nfl hP s hs)
  have hk := head_oadd_le hP'F hw hP'le hwp
  refine eq_of_summands_eq (wnf_oadd hpF (wnf_oadd hP'F hw)) (wnf_oadd (wnf_ofSummands hP) hw) ?_
  rw [summands_oadd_prin_keep hpF hpp (wnf_oadd hP'F hw) hk, summands_oadd_cons_keep hP hw hwp]

/-- 近似の引数の結合：`pre ⊕ (c ⊕ w) = (pre ++ c) ⊕ w`（吸収は `pre` に及ばない） -/
theorem apx_eq_oaddL : ∀ (pre : List Tm) {c w : Tm}, WNF c → WNF w → NFL (pre ++ summands c) →
    (∀ s, s ∈ pre → ∀ h r, summands w = h :: r → leB h s = true) →
    oadd (ofSummands pre) (oadd c w) = oadd (ofSummands (pre ++ summands c)) w
  | [], c, w, hc, hw, _, _ => by
    show oadd .zero (oadd c w) = oadd (ofSummands (summands c)) w
    rw [zero_oadd (wnf_oadd hc hw), ofSummands_summands c hc]
  | p :: P', c, w, hc, hw, hn, hwk => by
    have hP : NFL (p :: P') := nfl_append_left hn
    have hn' : NFL (P' ++ summands c) := nfl_tail hn
    have hcp : ∀ s, s ∈ summands c → leB s p = true := fun s hs =>
      leB_iff.mpr (le_head_of_nfl hn s (List.mem_append_right _ hs))
    have hwp := hwk p List.mem_cons_self
    have ih := apx_eq_oaddL P' hc hw hn' (fun s hs => hwk s (List.mem_cons_of_mem _ hs))
    rw [← oadd_cons_eq hP (wnf_oadd hc hw) (head_oadd_le hc hw hcp hwp), ih]
    have hQ : NFL (p :: (P' ++ summands c)) := hn
    rw [oadd_cons_eq hQ hw hwp]
    rfl

/-- 和の 0 番目：`(pre ++ [R])[0] = pre ⊕ R[0]`（`R` は後者でない） -/
theorem f0_split : ∀ (pre : List Tm) {B R : Tm}, WNF B → summands B = pre ++ [R] →
    ¬ isSucc R = true → fund B .zero = oadd (ofSummands pre) (fund R .zero)
  | [], B, R, hB, hs, _ => by
    have hRp : isPrincipal R = true := (summands_WNF B hB R (by rw [hs]; simp)).2
    have hBR : B = R := by
      have := ofSummands_summands B hB
      rw [hs] at this; exact this.symm
    subst hBR
    rw [show ofSummands ([] : List Tm) = .zero from rfl, zero_oadd (wnf_f0 hB)]
  | p :: P', B, R, hB, hs, hns => by
    have hn := nfl_summands hB
    rw [hs] at hn
    have hrest : P' ++ [R] ≠ [] := by simp
    have hBe := eq_plus_of_summands hB hs hrest
    obtain ⟨hB'F, hB's⟩ := tail_spec hB hs
    have hRF := hn.1 R (by simp)
    have hns' : ¬ isSucc (ofSummands (P' ++ [R])) = true := by
      have e := isSucc_of_last hB's hRF.2
      intro h; apply hns; rw [← e]; exact h
    have hd1 : dom (ofSummands (P' ++ [R])) ≠ .one := fun e => hns' ((dom_eq_one_iff hB'F).mp e)
    have ih := f0_split P' hB'F hB's hns
    have hB2 := hB
    rw [hBe] at hB2 ⊢
    rw [f0_plus hB2 hd1, ih]
    have hP : NFL (p :: P') := nfl_append_left (m := [R]) hn
    -- `R[0]` の先頭は `p` 以下
    have hRp : leB R p = true := leB_iff.mpr (le_head_of_nfl hn R (by simp))
    have hR0F := wnf_f0 hRF.1
    refine oadd_cons_eq hP hR0F (fun h r hr => ?_)
    have hR0 : R ≠ .zero := by intro e; rw [e] at hRF; cases hRF.2
    have hlt := f0_lt hRF.1 hR0
    have e1 := head_le_of_lt hr (summands_principal hRF.2) hlt
    have hhF := (summands_WNF _ hR0F h (by rw [hr]; exact List.mem_cons_self)).1
    have hhp := (summands_WNF _ hR0F h (by rw [hr]; exact List.mem_cons_self)).2
    have hpF := (hP.1 p List.mem_cons_self).1
    exact le_leB (le_transY hhF hRF.1 hpF
      (le_of_ne_gtY hhF hRF.1 (by rw [cmp_principal hhp hRF.2]; exact e1))
      (le_of_ne_gtY hRF.1 hpF (leB_iff.mp hRp)))

end MahloOCF.FS

/-! ### 崩壊の持ち上げの条件 -/

namespace MahloOCF.FS

open Tm

/-- 後者の引数の崩壊の 0 番目は `Ψ_π(X')` 以上（`Ξ` への崩壊では `X'` が下限より大きいとき） -/
theorem psi_succ_f0_ge {π B : Tm} (hB : WNF (.Psi π B)) (hs : isSucc B = true)
    (hv : ∀ m d, π = .Xi m d → Lt d (predT B)) : Le (.Psi π (predT B)) (fund (.Psi π B) .zero) := by
  rcases hB.psi.tgt with rfl | ⟨c, rfl, -⟩ | ⟨m, d, rfl⟩
  · rw [psiOm_succ_f0 hB hs]
    have hpF := psi_pred_WNF hB hs
    exact le_mulNat_two hpF rfl
  · rw [psiOm_succ_f0 hB hs]
    have hpF := psi_pred_WNF hB hs
    exact le_mulNat_two hpF rfl
  · exact Or.inr (psi_succ_xi_f0_gt hB hs (hv m d rfl))

/-- 近似の区間の `B` について `Ψ_π(A(x)) ≤ Ψ_π(B)[0]`（`A(z) = pre ⊕ (c ⊕ z)`、`c` は `0` か `rt + 1`） -/
theorem psi_harg_apx {π X R c x y B : Tm} {pre : List Tm}
    (ht : WNF (.Psi π X)) (hsX : summands X = pre ++ [R]) (hcF : WNF c) (hcR : Lt c R)
    (hcS : AdjShape π pre c) (hx : WNF x) (hy : WNF y) (hxy : Le x y) (hyR : Lt y R) (hL : LBI x y)
    (hA : WNF (.Psi π (apx pre c x)))
    (hB : WNF (.Psi π B)) (h1 : Lt (apx pre c x) B) (h2 : Le B (apx pre c y)) :
    Le (.Psi π (apx pre c x)) (fund (.Psi π B) .zero) := by
  have hP := ht.psi
  have hX := hP.aF
  have hXn : NFL (pre ++ [R]) := by rw [← hsX]; exact nfl_summands hX
  have hpre : NFL pre := nfl_append_left hXn
  have hPF := wnf_ofSummands hpre
  have hR := hXn.1 R (by simp)
  have hBF := hB.psi.aF
  have hAF := hA.psi.aF
  have hxR : Lt x R := lt_of_le_of_ltY hx hy hR.1 hxy hyR
  -- `pre` の加数は `R` 以上
  have hpreR : ∀ s, s ∈ pre → Le R s := fun s hs =>
    le_of_ne_gtY hR.1 (hpre.1 s hs).1 (nfl_append_ge hXn s hs R (by simp))
  -- `Q = pre ++ c`
  have hQ : NFL (pre ++ summands c) := by
    refine nfl_append hpre (nfl_summands hcF) (fun a b ha hb => ?_)
    have haF := (hpre.1 a (List.mem_of_getLast? ha)).1
    have hbF := (summands_WNF c hcF b (List.mem_of_mem_head? hb)).1
    have hbc : Le b c := le_of_mem_summands hcF (List.mem_of_mem_head? hb)
    have hbR : Lt b R := lt_of_le_of_ltY hbF hcF hR.1 hbc hcR
    exact ne_gt_of_le (Or.inr (lt_of_lt_of_leY hbF hR.1 haF hbR (hpreR a (List.mem_of_getLast? ha))))
  have hQF := wnf_ofSummands hQ
  have hapx : ∀ z, WNF z → Lt z R → apx pre c z = oadd (ofSummands (pre ++ summands c)) z := by
    intro z hz hzR
    refine apx_eq_oaddL pre hcF hz hQ (fun s hs h r hzs => ?_)
    have hhF := (summands_WNF z hz h (by rw [hzs]; exact List.mem_cons_self)).1
    have hhz : Le h z := le_of_mem_summands hz (by rw [hzs]; exact List.mem_cons_self)
    exact le_leB (Or.inr (lt_of_lt_of_leY hhF hR.1 (hpre.1 s hs).1
      (lt_of_le_of_ltY hhF hz hR.1 hhz hzR) (hpreR s hs)))
  have hB0 : B ≠ .zero := fun e => by rw [e] at h1; exact not_lt_zero _ h1
  by_cases hs : isSucc B = true
  · -- 後者
    have hp := le_pred_of_lt_succ hBF hs hAF h1
    have hv : ∀ m d, π = .Xi m d → Lt d (predT B) := by
      intro m d e
      have hdF : WNF d := by subst e; exact hP.piF.xi.2.1
      exact lt_of_lt_of_leY hdF hAF (predT_WNF hBF hs) (hA.psi.act m d e) hp
    have hpF : WNF (.Psi π (predT B)) := psi_pred_wnf hB hs hv
    exact le_transY hA hpF (wnf_f0 hB) (psi_le_psi hp) (psi_succ_f0_ge hB hs hv)
  · -- 極限：0 番目は `Ψ_π(pre_B ⊕ (c_B ⊕ x_B))`
    obtain ⟨preB, RB, hsB⟩ := exists_split hB0
    obtain ⟨cB, xB, he, hcBF, hxBF, hxB, hcBS⟩ := psi_lim_f0 hB hsB hs
    rw [he]
    have hBn : NFL (preB ++ [RB]) := by rw [← hsB]; exact nfl_summands hBF
    have hpreBF := wnf_ofSummands (nfl_append_left hBn)
    have hRB := hBn.1 RB (by simp)
    have hRBns : ¬ isSucc RB = true := by rw [← isSucc_of_last hsB hRB.2]; exact hs
    -- `B < X`
    have hyX : Lt (apx pre c y) X := by
      rw [eq_oadd_of_summands hX hsX]
      exact oadd_lt_oadd hPF (wnf_oadd hcF hy) hR.1 (oadd_lt_prin hcF hy hR.2 hcR hyR)
    have hBX : Lt B X := lt_of_le_of_ltY hBF (wnf_oadd hPF (wnf_oadd hcF hy)) hX h2 hyX
    rw [hapx x hx hxR] at h1 ⊢
    rw [hapx y hy hyR] at h2
    rcases gen_split (pre ++ summands c) hQ hx hy hBF hs hxy hL h1 h2 with hA' |
      ⟨Q₁, Q₂, b, hQe, hQ₂, hBs, hbp, hhead, hxb, hby⟩
    · -- `B[0]` 以上
      refine psi_le_psi (le_transY (wnf_oadd hQF hx) (wnf_f0 hBF) (wnf_oadd hpreBF (wnf_oadd hcBF hxBF)) hA' ?_)
      rw [f0_split preB hBF hsB hRBns]
      have hR0F := wnf_f0 hRB.1
      exact oadd_le_oadd hpreBF hR0F (wnf_oadd hcBF hxBF)
        (le_transY hR0F hxBF (wnf_oadd hcBF hxBF) hxB (le_oadd_right hcBF hxBF))
    · -- `B = Q₁ + b`：`B` の調整は `c` の残り
      have e1 : preB = Q₁ ∧ RB = b := by
        rw [hsB] at hBs
        have := List.append_inj' hBs rfl
        exact ⟨this.1, by simpa using this.2⟩
      obtain ⟨hpQ, hRb⟩ := e1
      subst preB
      subst RB
      have hbF := hRB.1
      -- `Q₁ = pre ++ C₁`、`c = C₁ ++ Q₂`
      obtain ⟨C₁, hQ1, hcs⟩ : ∃ C₁, Q₁ = pre ++ C₁ ∧ summands c = C₁ ++ Q₂ := by
        rcases List.append_eq_append_iff.mp hQe with ⟨as, h3, h4⟩ | ⟨bs, h3, h4⟩
        · exact ⟨as, h3, h4⟩
        · cases bs with
          | nil => exact ⟨[], by simp [h3], by simp [h4]⟩
          | cons b1 bs' =>
            exfalso
            have hb1 : Lt b1 b := hhead b1 (by rw [h4]; rfl)
            have hb1p := (hpre.1 b1 (by rw [h3]; simp)).2
            have hXs : summands X = Q₁ ++ (b1 :: (bs' ++ [R])) := by rw [hsX, h3]; simp
            have hBs' : summands B = Q₁ ++ [b] := hsB
            have hgt : Lt X B := by
              unfold Lt
              rw [cmp_eq, hXs, hBs', cmpList_append_same]
              have e : cmpP b1 b = .lt := by
                have := hb1; unfold Lt at this; rwa [cmp_principal hb1p hbp] at this
              rw [cmpList_cons_cons_ne _ _ (by rw [e]; decide), e]
            exact Lt.asymmY hX hBF hgt hBX
      -- `c ≠ 0` なので `c = rt + 1`
      have hc0 : summands c ≠ [] := by rw [hcs]; exact List.append_ne_nil_of_right_ne_nil _ hQ₂
      rcases hcS with ⟨hc0', -⟩ | ⟨rt, hrt, hcrt⟩
      · exact absurd (by rw [hc0']; rfl) hc0
      cases hδ : argR? π with
      | none => rw [hδ] at hrt; simp [tailRaw] at hrt
      | some δ =>
        obtain ⟨m, rfl⟩ := argR_some hδ
        rw [hδ] at hrt
        have hδF := hP.piF.xi.2.1
        obtain ⟨hrtF, hsδ, -⟩ := tailRaw_some hδF hrt
        obtain ⟨Q₂', t, hQ₂e⟩ : ∃ Q₂' t, Q₂ = Q₂' ++ [t] :=
          ⟨Q₂.dropLast, Q₂.getLast hQ₂, (List.dropLast_concat_getLast hQ₂).symm⟩
        have hrts : summands rt = C₁ ++ Q₂' ∧ [one] = [t] := by
          have := hcs
          rw [hcrt, show sc rt = succT rt from rfl, summands_succT, hQ₂e, ← List.append_assoc] at this
          exact List.append_inj' this rfl
        have ht1 : t = one := by have := hrts.2; simp at this; exact this.symm
        have hQ₂'p : ∀ s, s ∈ Q₂' → isPrincipal s = true := fun s hs =>
          (summands_WNF rt hrtF s (by rw [hrts.1]; exact List.mem_append_right _ hs)).2
        have hrtBs : summands (ofSummands Q₂') = Q₂' := summands_ofSummands Q₂' hQ₂'p
        -- `δ` は `Q₁` で始まる
        have hδs : summands δ = Q₁ ++ Q₂' := by rw [hsδ, hrts.1, hQ1, List.append_assoc]
        have htr : tailRaw (some δ) Q₁ = some (ofSummands Q₂') := by
          unfold tailRaw
          dsimp only
          rw [hδs, if_pos ⟨by simp, List.take_left' rfl⟩, List.drop_left' rfl]
        -- `B` の調整は `rt_B + 1`
        have hcB : cB = sc (ofSummands Q₂') := by
          rcases hcBS with ⟨-, hn⟩ | ⟨rt', hrt', hc'⟩
          · rw [show argR? (Tm.Xi m δ) = some δ from rfl, htr] at hn; cases hn
          · rw [show argR? (Tm.Xi m δ) = some δ from rfl, htr] at hrt'
            cases hrt'; exact hc'
        subst hcB
        have hrtBF : WNF (ofSummands Q₂') := by
          have hn := nfl_summands hrtF
          rw [hrts.1] at hn
          exact wnf_ofSummands (nfl_append_right hn)
        have hscs : summands (sc (ofSummands Q₂')) = Q₂ := by
          show summands (succT (ofSummands Q₂')) = Q₂
          rw [summands_succT, hrtBs, hQ₂e, ht1]
        -- `x` の先頭は `Q₁` の加数以下
        have hxQ1 : ∀ s, s ∈ Q₁ → ∀ h r, summands x = h :: r → leB h s = true := by
          intro s hs h r hxs
          have hsF := (hBn.1 s (List.mem_append_left _ hs)).1
          have hhF := (summands_WNF x hx h (by rw [hxs]; exact List.mem_cons_self)).1
          have hhx : Le h x := le_of_mem_summands hx (by rw [hxs]; exact List.mem_cons_self)
          have hbs : Le b s := le_of_ne_gtY hbF hsF (nfl_append_ge hBn s hs b (by simp))
          exact le_leB (Or.inr (lt_of_lt_of_leY hhF hbF hsF (lt_of_le_of_ltY hhF hx hbF hhx hxb) hbs))
        have hQ1n : NFL (Q₁ ++ summands (sc (ofSummands Q₂'))) := by
          rw [hscs, ← hQe]; exact hQ
        have e2 : oadd (ofSummands (pre ++ summands c)) x = apx Q₁ (sc (ofSummands Q₂')) x := by
          rw [hQe, ← hscs]
          exact (apx_eq_oaddL Q₁ (succT_WNF hrtBF) hx hQ1n hxQ1).symm
        rw [e2]
        -- `x ≤ x_B`
        have hxxB : Le x xB := le_transY hx (wnf_f0 hbF) hxBF (hL b hbF hxb hby) hxB
        have hsF := succT_WNF hrtBF
        exact psi_le_psi (oadd_le_oadd hpreBF (wnf_oadd hsF hx) (wnf_oadd hsF hxBF)
          (oadd_le_oadd hsF hx hxBF hxxB))

end MahloOCF.FS
