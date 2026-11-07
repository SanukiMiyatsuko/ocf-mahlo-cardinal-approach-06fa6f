import Mahlo.WF.Syntax

/-! 体系全体の順序の性質の構文的な証明（Compact リポジトリの `Compact/WF/Order.lean` と同じ構成）。

部分項で閉じた有限集合 `S` の要素数についての帰納法で不変条件 `GoodY S` を示す。

不変条件：
* `LinOn S`・`AntiOn S`：`S` の上で `<` は推移的、`cmp` は反対称で `.eq` なら等しい。
* `K2On S`・`K2TOn S`：`Ψ_π(γ) ∈ S` の引数・崩壊先の前線（`π` について）は `Ψ_π(γ)` 未満。
* `K2XOn S`：`Ξ_n(γ) ∈ S` の引数の前線（`M_n` について）は `Ξ_n(γ)` 未満。
* `CXOn S`：`Ψ_{Ω_c}(γ) ∈ S`（`c` は後者）について `c < Ψ_{Ω_c}(γ)`。 -/

namespace MahloOCF

open Tm

/-- `S` の上の反対称性と相等 -/
def AntiOn (S : List Tm) : Prop :=
  ∀ a, a ∈ S → ∀ b, b ∈ S → cmp b a = (cmp a b).swap ∧ (cmp a b = .eq → a = b)

def K2On (S : List Tm) : Prop :=
  ∀ π γ, Tm.Psi π γ ∈ S → ∀ w, w ∈ fr π γ → Lt w (.Psi π γ)

def K2TOn (S : List Tm) : Prop :=
  ∀ π γ, Tm.Psi π γ ∈ S → ∀ w, w ∈ fr π π → Lt w (.Psi π γ)

def K2XOn (S : List Tm) : Prop :=
  ∀ n γ, Tm.Xi n γ ∈ S → ∀ w, w ∈ fr (.M n) γ → Lt w (.Xi n γ)

def CXOn (S : List Tm) : Prop :=
  ∀ c γ, Tm.Psi (.Om c) γ ∈ S → isSucc c = true → Lt c (.Psi (.Om c) γ)

/-- 順序の性質の証明の不変条件 -/
structure GoodY (S : List Tm) : Prop where
  lin : LinOn S
  anti : AntiOn S
  nf : ∀ s, s ∈ S → WNF s
  cl : ∀ s, s ∈ S → ∀ r, r ∈ subs s → r ∈ S
  k2 : K2On S
  k2t : K2TOn S
  k2x : K2XOn S
  cx : CXOn S

namespace GoodY

variable {S : List Tm} (G : GoodY S)
include G

theorem sub {s r : Tm} (hs : s ∈ S) (hr : r ∈ subs s) : r ∈ S := G.cl s hs r hr

theorem trans {a b c : Tm} (ha : a ∈ S) (hb : b ∈ S) (hc : c ∈ S) (h1 : Lt a b) (h2 : Lt b c) :
    Lt a c :=
  G.lin a ha b hb c hc h1 h2

theorem swap {a b : Tm} (ha : a ∈ S) (hb : b ∈ S) : cmp b a = (cmp a b).swap :=
  (G.anti a ha b hb).1

theorem eq {a b : Tm} (ha : a ∈ S) (hb : b ∈ S) (h : cmp a b = .eq) : a = b :=
  (G.anti a ha b hb).2 h

theorem asymm {a b : Tm} (ha : a ∈ S) (hb : b ∈ S) (h : Lt a b) : ¬ Lt b a := by
  unfold Lt at *
  rw [G.swap ha hb, h]
  decide

theorem lt_of_gt {a b : Tm} (ha : a ∈ S) (hb : b ∈ S) (h : cmp a b = .gt) : Lt b a := by
  unfold Lt
  rw [G.swap ha hb, h]
  rfl

theorem tri {a b : Tm} (ha : a ∈ S) (hb : b ∈ S) : Lt a b ∨ a = b ∨ Lt b a := by
  cases e : cmp a b with
  | lt => exact Or.inl e
  | eq => exact Or.inr (Or.inl (G.eq ha hb e))
  | gt => exact Or.inr (Or.inr (G.lt_of_gt ha hb e))

/-- `¬ a < b` なら `b ≤ a` -/
theorem le_of_not_lt {a b : Tm} (ha : a ∈ S) (hb : b ∈ S) (h : ¬ Lt a b) : Le b a := by
  rcases G.tri ha hb with h' | h' | h'
  · exact absurd h' h
  · exact Or.inl h'.symm
  · exact Or.inr h'

theorem le_of_ne_gt {a b : Tm} (ha : a ∈ S) (hb : b ∈ S) (h : cmp a b ≠ .gt) : Le a b := by
  cases e : cmp a b with
  | lt => exact Or.inr e
  | eq => exact Or.inl (G.eq ha hb e)
  | gt => exact absurd e h

theorem not_lt_of_le {a b : Tm} (ha : a ∈ S) (hb : b ∈ S) (h : Le a b) : ¬ Lt b a := by
  rcases h with rfl | h
  · exact Lt.irrefl _
  · exact G.asymm ha hb h

theorem lt_of_lt_of_le {a b c : Tm} (ha : a ∈ S) (hb : b ∈ S) (hc : c ∈ S) (h1 : Lt a b)
    (h2 : Le b c) : Lt a c := by
  rcases h2 with rfl | h2
  · exact h1
  · exact G.trans ha hb hc h1 h2

theorem lt_of_le_of_lt {a b c : Tm} (ha : a ∈ S) (hb : b ∈ S) (hc : c ∈ S) (h1 : Le a b)
    (h2 : Lt b c) : Lt a c := by
  rcases h1 with rfl | h1
  · exact h2
  · exact G.trans ha hb hc h1 h2

theorem le_trans {a b c : Tm} (ha : a ∈ S) (hb : b ∈ S) (hc : c ∈ S) (h1 : Le a b)
    (h2 : Le b c) : Le a c := by
  rcases h1 with rfl | h1
  · exact h2
  · exact Or.inr (G.lt_of_lt_of_le ha hb hc h1 h2)

theorem eq_of_cmpP_eq {x y : Tm} (hx : x ∈ S) (hy : y ∈ S) (hpx : isPrincipal x = true)
    (hpy : isPrincipal y = true) (h : cmpP x y = .eq) : x = y := by
  apply G.eq hx hy
  rw [cmp_principal hpx hpy, h]

end GoodY

/-! ## 切断性の枠組み -/

/-- 底は同じ階の底でない主要項より小さい -/
theorem lt_of_isBotY {x y : Tm} (hl : lev x = lev y) (hx : isBot x = true) (hy : isBot y = false)
    (hpy : isPrincipal y = true) (hyF : WNF y) : cmpP x y = .lt := by
  cases x with
  | M m =>
    rw [cmpP.eq_def]
    simp only [hl, Nat.lt_irrefl, ↓reduceIte]
    cases y with
    | M _ => simp [isBot] at hy
    | Om b =>
      have hb : b ≠ .M m := by
        intro e; subst e; have := hyF.om.2; simp [omegaFixed] at this
      simp [hb]
    | zero => simp [isPrincipal] at hpy
    | plus _ _ => simp [isPrincipal] at hpy
    | _ => simp
  | _ => simp [isBot] at hx

/-- 底は同じ階以上の底でない主要項より小さい -/
theorem bot_ltY {h t : Tm} (hb : isBot h = true) (hl : lev h ≤ lev t) (htp : isPrincipal t = true)
    (htb : isBot t = false) (ht : WNF t) : Lt h t := by
  have hp : isPrincipal h = true := by cases h <;> simp_all [isBot, isPrincipal]
  rcases Nat.lt_or_eq_of_le hl with hl | hl
  · exact lt_of_lev_lt' hl
  · exact (lt_principal_iff hp htp).mpr (lt_of_isBotY hl hb htb htp ht)

namespace GoodY

variable {S : List Tm} (G : GoodY S)
include G

theorem lexTrans : ∀ l1 l2 l3 : List Tm,
    (∀ x, x ∈ l1 → x ∈ S ∧ isPrincipal x = true) →
    (∀ x, x ∈ l2 → x ∈ S ∧ isPrincipal x = true) →
    (∀ x, x ∈ l3 → x ∈ S ∧ isPrincipal x = true) →
    cmpList l1 l2 = .lt → cmpList l2 l3 = .lt → cmpList l1 l3 = .lt
  | [], [], _, _, _, _, h, _ => by rw [cmpList_nil_nil] at h; cases h
  | [], _ :: _, [], _, _, _, _, h => by rw [cmpList_cons_nil] at h; cases h
  | [], _ :: _, _ :: _, _, _, _, _, _ => cmpList_nil_cons _ _
  | _ :: _, [], _, _, _, _, h, _ => by rw [cmpList_cons_nil] at h; cases h
  | _ :: _, _ :: _, [], _, _, _, _, h => by rw [cmpList_cons_nil] at h; cases h
  | x :: xs, y :: ys, z :: zs, h1, h2, h3, hxy, hyz => by
    have hx := h1 x List.mem_cons_self
    have hy := h2 y List.mem_cons_self
    have hz := h3 z List.mem_cons_self
    rcases cmpList_lt_cases hxy with e1 | ⟨e1, r1⟩ <;> rcases cmpList_lt_cases hyz with e2 | ⟨e2, r2⟩
    · have : Lt x z := G.trans hx.1 hy.1 hz.1 ((lt_principal_iff hx.2 hy.2).mpr e1)
        ((lt_principal_iff hy.2 hz.2).mpr e2)
      rw [lt_principal_iff hx.2 hz.2] at this
      rw [cmpList_cons_cons_ne _ _ (by rw [this]; decide), this]
    · have := G.eq_of_cmpP_eq hy.1 hz.1 hy.2 hz.2 e2
      subst this
      rw [cmpList_cons_cons_ne _ _ (by rw [e1]; decide), e1]
    · have := G.eq_of_cmpP_eq hx.1 hy.1 hx.2 hy.2 e1
      subst this
      rw [cmpList_cons_cons_ne _ _ (by rw [e2]; decide), e2]
    · have := G.eq_of_cmpP_eq hx.1 hy.1 hx.2 hy.2 e1
      subst this
      have := G.eq_of_cmpP_eq hx.1 hz.1 hx.2 hz.2 e2
      subst this
      rw [cmpList_cons_cons_eq _ _ (cmpP_self x)]
      exact lexTrans xs ys zs (fun w hw => h1 w (List.mem_cons_of_mem _ hw))
        (fun w hw => h2 w (List.mem_cons_of_mem _ hw)) (fun w hw => h3 w (List.mem_cons_of_mem _ hw))
        r1 r2

/-- 一般の項 `t` の切断性：主要項の組についての切断性 `hP` から -/
theorem cutGen {t : Tm} (ht : WNF t) (hsub : ∀ s, s ∈ subs t → s ≠ t → s ∈ S)
    {a b : Tm}
    (hP : isPrincipal t = true → ∀ q p, q ∈ summands b → p ∈ summands a →
      Lt q p → Lt p t → Lt q t)
    (ha : a ∈ S) (hb : b ∈ S) (h1 : Lt b a) (h2 : Lt a t) : Lt b t := by
  have hsa : ∀ x, x ∈ summands a → x ∈ S ∧ isPrincipal x = true := fun x hx =>
    ⟨G.sub ha (mem_subs_of_mem_summands hx), (summands_WNF a (G.nf a ha) x hx).2⟩
  have hsb : ∀ x, x ∈ summands b → x ∈ S ∧ isPrincipal x = true := fun x hx =>
    ⟨G.sub hb (mem_subs_of_mem_summands hx), (summands_WNF b (G.nf b hb) x hx).2⟩
  unfold Lt at h1 h2 ⊢
  rw [cmp_eq] at h1 h2 ⊢
  cases htp : isPrincipal t
  · cases t with
    | zero =>
      exfalso
      cases hs : summands a with
      | nil => rw [hs, summands, cmpList_nil_nil] at h2; cases h2
      | cons _ _ => rw [hs, summands, cmpList_cons_nil] at h2; cases h2
    | plus h r =>
      have hst : ∀ x, x ∈ summands (.plus h r) → x ∈ S ∧ isPrincipal x = true := by
        intro x hx
        refine ⟨hsub x (mem_subs_of_mem_summands hx) ?_, (summands_WNF _ ht x hx).2⟩
        intro e
        subst e
        rw [summands, List.mem_cons] at hx
        rcases hx with hx | hx
        · have := congrArg Tm.size hx
          simp only [Tm.size] at this
          omega
        · have := size_le_of_mem_subs (mem_subs_of_mem_summands hx)
          simp only [Tm.size] at this
          omega
      exact G.lexTrans _ _ _ hsb hsa hst h1 h2
    | _ => simp [isPrincipal] at htp
  · rw [summands_principal htp] at h2 ⊢
    cases hsb' : summands b with
    | nil => exact cmpList_nil_cons _ _
    | cons q qs =>
      cases hsa' : summands a with
      | nil => rw [hsb', hsa', cmpList_cons_nil] at h1; cases h1
      | cons p ps =>
        rw [hsb', hsa'] at h1
        rw [hsa'] at h2
        have hp := hsa p (by rw [hsa']; exact List.mem_cons_self)
        have hq := hsb q (by rw [hsb']; exact List.mem_cons_self)
        have hpt : cmpP p t = .lt := by
          rcases cmpList_lt_cases h2 with e | ⟨_, e⟩
          · exact e
          · cases ps with
            | nil => rw [cmpList_nil_nil] at e; cases e
            | cons _ _ => rw [cmpList_cons_nil] at e; cases e
        have hqt : cmpP q t = .lt := by
          rcases cmpList_lt_cases h1 with e | ⟨e, _⟩
          · rw [← lt_principal_iff hq.2 htp]
            exact hP htp q p (by rw [hsb']; exact List.mem_cons_self)
              (by rw [hsa']; exact List.mem_cons_self)
              ((lt_principal_iff hq.2 hp.2).mpr e) ((lt_principal_iff hp.2 htp).mpr hpt)
          · have := G.eq_of_cmpP_eq hq.1 hp.1 hq.2 hp.2 e
            subst this
            exact hpt
        rw [cmpList_cons_cons_ne _ _ (by rw [hqt]; decide), hqt]

/-- 主要項の組についての切断性から一般の切断性へ（大きさの和についての帰納法） -/
theorem cut_of_principal {t : Tm} (ht : WNF t)
    (hsub : ∀ s, s ∈ subs t → s ≠ t → s ∈ S)
    (hP : ∀ N, (∀ a b, a ∈ S → b ∈ S → a.size + b.size < N → Lt b a → Lt a t → Lt b t) →
      isPrincipal t = true → ∀ q p, q ∈ S → p ∈ S → isPrincipal q = true →
        isPrincipal p = true → q.size + p.size ≤ N → Lt q p → Lt p t → Lt q t) :
    CutT S t := by
  have key : ∀ N, ∀ a b, a ∈ S → b ∈ S → a.size + b.size ≤ N → Lt b a → Lt a t → Lt b t := by
    intro N
    induction N with
    | zero =>
      intro a _ _ _ h
      have := Tm.size_pos a
      omega
    | succ N ih =>
      intro a b ha hb hs h1 h2
      refine G.cutGen ht hsub (fun htp q p hq hp => ?_) ha hb h1 h2
      exact hP (a.size + b.size) (fun a' b' ha' hb' hs' => ih a' b' ha' hb' (by omega)) htp q p
        (G.sub hb (mem_subs_of_mem_summands hq)) (G.sub ha (mem_subs_of_mem_summands hp))
        (summands_WNF b (G.nf b hb) q hq).2 (summands_WNF a (G.nf a ha) p hp).2
        (by have := size_le_of_mem_summands b q hq; have := size_le_of_mem_summands a p hp; omega)
  exact fun a b ha hb => key _ a b ha hb (Nat.le_refl _)

end GoodY

/-- 主要項の組の場合分けの前処理：階が下がる場合と底の場合を片付ける -/
theorem cut_reduceY {t : Tm} (ht : WNF t) (htp : isPrincipal t = true) (htb : isBot t = false)
    {q p : Tm} (hq : WNF q) (hp : WNF p) (hqp : isPrincipal q = true)
    (hpp : isPrincipal p = true) (h1 : Lt q p) (h2 : Lt p t)
    (core : lev q = lev t → lev p = lev t → isBot q = false → isBot p = false → Lt q t) :
    Lt q t := by
  have l1 := lev_le_of_lt_gen h1
  have l2 := lev_le_of_lt_gen h2
  by_cases hl : lev q < lev t
  · exact lt_of_lev_lt' hl
  have lq : lev q = lev t := by omega
  have lp : lev p = lev t := by omega
  cases hbq : isBot q
  · cases hbp : isBot p
    · exact core lq lp hbq hbp
    · exact absurd ((lt_principal_iff hqp hpp).mp h1) (not_lt_isBotY (by omega) hbp hq hp)
  · exact (lt_principal_iff hqp htp).mpr (lt_of_isBotY (by omega) hbq htb htp ht)

/-- 底（`M_n`）や `0` は切断する -/
theorem cut_botY {S : List Tm} (G : GoodY S) {t : Tm} (ht : WNF t)
    (htb : isBot t = true ∨ t = .zero)
    (hsub : ∀ s, s ∈ subs t → s ≠ t → s ∈ S) : CutT S t := by
  refine G.cut_of_principal ht hsub (fun _ _ htp q p hqS hpS hqp hpp _ h1 h2 => ?_)
  have hpF := G.nf p hpS
  rcases htb with htb | rfl
  · have l1 := lev_le_of_lt_gen h1
    have l2 := lev_le_of_lt_gen h2
    rcases Nat.lt_or_eq_of_le l2 with l2 | l2
    · exact lt_of_lev_lt' (by omega)
    · exact absurd ((lt_principal_iff hpp htp).mp h2) (not_lt_isBotY l2 htb hpF ht)
  · exact absurd h2 (not_lt_zero p)

/-! ## 前線の片方向の言い換え -/

/-- 前線の各節点が `C(g, d)` に入り、`R` 以上の節点の引数が `g0` 未満（したがって `g` 未満）なら、
    `x ∈ C(g, d)` -/
theorem inC_of_fr {R g0 g d : Tm} : ∀ x : Tm, inC x g0 R = true →
    (∀ v, v ∈ subs x → Lt v g0 → Lt v g) →
    (∀ w, w ∈ fr R x → inC w g d = true) → inC x g d = true
  | .zero, _, _, _ => inC_zero _ _
  | .M n, _, _, _ => inC_M n _ _
  | .plus a b, h0, hg, hw => by
    rw [inC_plus, Bool.and_eq_true] at h0 ⊢
    exact ⟨inC_of_fr a h0.1 (fun v hv => hg v (subs_plus_l hv))
        (fun w h => hw w (by rw [fr, List.mem_append]; exact Or.inl h)),
      inC_of_fr b h0.2 (fun v hv => hg v (subs_plus_r hv))
        (fun w h => hw w (by rw [fr, List.mem_append]; exact Or.inr h))⟩
  | .Om a, h0, hg, hw => by
    rw [inC_om] at h0 ⊢
    exact inC_of_fr a h0 (fun v hv => hg v (subs_om hv)) (fun w h => hw w (by rw [fr]; exact h))
  | .Xi m a, h0, hg, hw => by
    by_cases hR : Lt (.Xi m a) R
    · exact hw _ (by rw [fr]; simp [hR])
    · rcases inC_xi_iff.mp h0 with h | ⟨ha, hlt⟩
      · exact absurd h hR
      · exact inC_xi_iff.mpr (Or.inr ⟨inC_of_fr a ha (fun v hv => hg v (subs_xi hv))
          (fun w h => hw w (by rw [fr]; simp only [hR, ↓reduceIte]; exact h)),
          hg a (mem_subs_xi m a) hlt⟩)
  | .Psi p a, h0, hg, hw => by
    by_cases hR : Lt (.Psi p a) R
    · exact hw _ (by rw [fr]; simp [hR])
    · rcases inC_psi_iff.mp h0 with h | ⟨hp, ha, hlt⟩
      · exact absurd h hR
      · have hw' : ∀ w, w ∈ fr R p ++ fr R a → inC w g d = true := fun w h =>
          hw w (by rw [fr]; simp only [hR, ↓reduceIte]; exact h)
        refine inC_psi_iff.mpr (Or.inr ⟨?_, ?_, hg a (mem_subs_psi_a p a) hlt⟩)
        · exact inC_of_fr p hp (fun v hv => hg v (subs_psi_p hv)) (fun w h => hw' w (by simp [h]))
        · exact inC_of_fr a ha (fun v hv => hg v (subs_psi_a hv)) (fun w h => hw' w (by simp [h]))

/-- `R` 以上の節点が `d` 未満でなければ、`x ∈ C(g, d)` から前線の各節点が `C(g, d)` に入る -/
theorem fr_of_inC {R g d : Tm} : ∀ x : Tm,
    (∀ w, w ∈ subs x → ¬ Lt w R → ¬ Lt w d) → inC x g d = true →
    ∀ w, w ∈ fr R x → inC w g d = true
  | .zero, _, _, w, h | .M _, _, _, w, h => by simp [fr] at h
  | .plus a b, hd, hx, w, h => by
    rw [inC_plus, Bool.and_eq_true] at hx
    rw [fr, List.mem_append] at h
    rcases h with h | h
    · exact fr_of_inC a (fun v hv => hd v (subs_plus_l hv)) hx.1 w h
    · exact fr_of_inC b (fun v hv => hd v (subs_plus_r hv)) hx.2 w h
  | .Om a, hd, hx, w, h => by
    rw [inC_om] at hx
    rw [fr] at h
    exact fr_of_inC a (fun v hv => hd v (subs_om hv)) hx w h
  | .Xi m a, hd, hx, w, h => by
    rw [fr] at h
    by_cases hR : Lt (.Xi m a) R
    · simp only [hR, ↓reduceIte, List.mem_singleton] at h
      subst h
      exact hx
    · simp only [hR, ↓reduceIte] at h
      rcases inC_xi_iff.mp hx with h' | ⟨ha, _⟩
      · exact absurd h' (hd _ (self_mem_subs _) hR)
      · exact fr_of_inC a (fun v hv => hd v (subs_xi hv)) ha w h
  | .Psi p a, hd, hx, w, h => by
    rw [fr] at h
    by_cases hR : Lt (.Psi p a) R
    · simp only [hR, ↓reduceIte, List.mem_singleton] at h
      subst h
      exact hx
    · simp only [hR, ↓reduceIte, List.mem_append] at h
      rcases inC_psi_iff.mp hx with h' | ⟨hp, ha, _⟩
      · exact absurd h' (hd _ (self_mem_subs _) hR)
      · rcases h with h | h
        · exact fr_of_inC p (fun v hv => hd v (subs_psi_p hv)) hp w h
        · exact fr_of_inC a (fun v hv => hd v (subs_psi_a hv)) ha w h

/-- `x ∉ C(g, d)` なら前線に `d` 未満でない節点がある -/
theorem wit_of_not_inC {R g0 g d x : Tm} (h0 : inC x g0 R = true)
    (hg : ∀ v, v ∈ subs x → Lt v g0 → Lt v g) (hn : inC x g d = false) :
    ∃ w, w ∈ fr R x ∧ ¬ Lt w d := by
  by_cases h : ∀ w, w ∈ fr R x → inC w g d = true
  · rw [inC_of_fr x h0 hg h] at hn
    cases hn
  · obtain ⟨w, hw, hw'⟩ := exists_of_not_forall_mem _ h
    exact ⟨w, hw, fun h' => hw' (inC_of_lt_node (fr_node hw) h')⟩

/-- 前線の取り替え：`x` の部分項について `v < R' → v < R` なら、`R` についての前線の `R'` 未満の元は
    `R'` についての前線の元 -/
theorem fr_subG {R R' : Tm} : ∀ {x w : Tm}, (∀ v, v ∈ subs x → Lt v R' → Lt v R) →
    w ∈ fr R x → Lt w R' → w ∈ fr R' x
  | .zero, _, _, h, _ | .M _, _, _, h, _ => by simp [fr] at h
  | .plus a b, w, hR, h, hw => by
    rw [fr, List.mem_append] at h ⊢
    rcases h with h | h
    · exact Or.inl (fr_subG (fun v hv => hR v (subs_plus_l hv)) h hw)
    · exact Or.inr (fr_subG (fun v hv => hR v (subs_plus_r hv)) h hw)
  | .Om a, w, hR, h, hw => by
    rw [fr] at h ⊢
    exact fr_subG (fun v hv => hR v (subs_om hv)) h hw
  | .Xi m a, w, hR, h, hw => by
    rw [fr] at h ⊢
    by_cases hl : Lt (.Xi m a) R
    · simp only [hl, ↓reduceIte, List.mem_singleton] at h
      subst h
      simp only [hw, ↓reduceIte, List.mem_singleton]
    · simp only [hl, ↓reduceIte] at h
      have hl' : ¬ Lt (.Xi m a) R' := fun h' => hl (hR _ (self_mem_subs _) h')
      simp only [hl', ↓reduceIte]
      exact fr_subG (fun v hv => hR v (subs_xi hv)) h hw
  | .Psi p a, w, hR, h, hw => by
    rw [fr] at h ⊢
    by_cases hl : Lt (.Psi p a) R
    · simp only [hl, ↓reduceIte, List.mem_singleton] at h
      subst h
      simp only [hw, ↓reduceIte, List.mem_singleton]
    · simp only [hl, ↓reduceIte, List.mem_append] at h
      have hl' : ¬ Lt (.Psi p a) R' := fun h' => hl (hR _ (self_mem_subs _) h')
      simp only [hl', ↓reduceIte, List.mem_append]
      rcases h with h | h
      · exact Or.inl (fr_subG (fun v hv => hR v (subs_psi_p hv)) h hw)
      · exact Or.inr (fr_subG (fun v hv => hR v (subs_psi_a hv)) h hw)

/-! ## `Ξ` の崩壊の性質（順序の仮定なし） -/

/-- `Ξ_n(γ)` の崩壊の性質：`z ∈ C(γ, Ξ_n(γ))` で `z < M_n` なら `z < Ξ_n(γ)` -/
theorem coll_xi0 {n : Nat} {γ : Tm} (ht : WNF (.Xi n γ)) :
    ∀ z, WNF z → inC z γ (.Xi n γ) = true → Lt z (.M n) → Lt z (.Xi n γ) := by
  obtain ⟨hn, -, -, -⟩ := ht.xi
  have hX : IsOF (.Xi n γ) := Or.inl ⟨n, γ, rfl⟩
  intro z
  induction z with
  | zero => intros; exact zero_lt (by intro e; cases e)
  | M m =>
    intro hz _ hlt
    exact bot_ltY rfl ((lt_M_iffY hz hn).mp hlt) rfl rfl ht
  | plus a b iha _ =>
    intro hz hin hlt
    rw [inC_plus, Bool.and_eq_true] at hin
    obtain ⟨haF, -, -, -⟩ := hz.plus
    have hl := (lt_M_iffY hz hn).mp hlt
    exact (lt_plus_prin_iffY hz rfl).mpr (iha haF hin.1 ((lt_M_iffY haF hn).mpr hl))
  | Om g ihg =>
    intro hz hin hlt
    rw [inC_om] at hin
    have hgF := hz.om.1
    have hl := (lt_M_iffY hz hn).mp hlt
    simp only [lev] at hl
    exact (lt_om_OFG hX ht).mpr (ihg hgF hin ((lt_M_iffY hgF hn).mpr (by omega)))
  | Xi m f _ =>
    intro hz hin hlt
    rcases inC_xi_iff.mp hin with h | ⟨hf, hfγ⟩
    · exact h
    have hl := (lt_M_iffY hz hn).mp hlt
    simp only [lev] at hl
    rcases Nat.lt_or_eq_of_le hl with hl | hl
    · exact lt_of_lev_lt' (by simp only [lev]; exact hl)
    · subst hl
      have hne : f ≠ γ := fun e => by subst e; exact Lt.irrefl _ hfγ
      rw [lt_principal_iff rfl rfl, cmpP_xi_xi, xiLtXi_eq]
      unfold Lt at hfγ
      simp [hne, hfγ, hf]
  | Psi κ β ihκ _ =>
    intro hz hin hlt
    have hκF := hz.psi.piF
    rcases inC_psi_iff.mp hin with h | ⟨hκ, -, -⟩
    · exact h
    have hl := (lt_M_iffY hz hn).mp hlt
    simp only [lev] at hl
    rcases Nat.lt_or_eq_of_le hl with hl | hl
    · exact lt_of_lev_lt' (by simp only [lev]; exact hl)
    · have hκX := ihκ hκF hκ ((lt_M_iffY hκF hn).mpr (by omega))
      refine (lt_psi_xiY hl).mpr (Or.inl ?_)
      unfold Lt at hκX
      rw [hκX]
      decide

end MahloOCF

/-! ## `S` の中の比較 -/

namespace MahloOCF

open Tm

namespace GoodY

variable {S : List Tm} (G : GoodY S)
include G

theorem lt_om_iffS {a b : Tm} (ha : a ∈ S) (hb : b ∈ S) : Lt (.Om a) (.Om b) ↔ Lt a b := by
  rcases Nat.lt_trichotomy (max 1 (lev a)) (max 1 (lev b)) with h | h | h
  · constructor
    · intro _; exact lt_of_lev_lt' (by omega)
    · intro _
      rw [lt_principal_iff rfl rfl, cmpP_of_lev_lt (by simp only [lev]; exact h)]
  · rw [lt_principal_iff rfl rfl, cmpP_om_om h]; rfl
  · constructor
    · intro h'
      rw [lt_principal_iff rfl rfl, cmpP_of_lev_gt (by simp only [lev]; exact h)] at h'
      cases h'
    · intro h'; exact absurd (lt_of_lev_lt' (by omega)) (G.asymm ha hb h')

theorem le_om_iffS {a b : Tm} (ha : a ∈ S) (hb : b ∈ S) : Le (.Om a) (.Om b) ↔ Le a b := by
  constructor
  · rintro (e | h)
    · cases e; exact Or.inl rfl
    · exact Or.inr ((G.lt_om_iffS ha hb).mp h)
  · rintro (rfl | h)
    · exact Or.inl rfl
    · exact Or.inr ((G.lt_om_iffS ha hb).mpr h)

/-- `Ω` の不動点 `X` と `Ω_e`：`X < Ω_e` ⟺ `X < e` -/
theorem lt_OF_omS {X e : Tm} (hX : IsOF X) (hXS : X ∈ S) (heS : e ∈ S) :
    Lt X (.Om e) ↔ Lt X e := by
  have hX1 := hX.lev_pos (G.nf X hXS)
  rcases Nat.lt_trichotomy (max 1 (lev e)) (lev X) with hl | hl | hl
  · constructor
    · intro h; have := lev_le_of_lt_gen h; simp only [lev] at this; exfalso; omega
    · intro h; have := lev_le_of_lt_gen h; exfalso; omega
  · rw [lt_principal_iff hX.principal rfl, cmpP_OF_om hX hl]
    unfold Lt
    rw [G.swap hXS heS]
    cases cmp X e <;> simp
  · exact ⟨fun _ => lt_of_lev_lt' (by omega), fun _ => lt_of_lev_lt' (by simp only [lev]; exact hl)⟩

/-- `Ψ_{Ω_c}(β) < Ω_e` ⟺ `c ≤ e` -/
theorem lt_psiOm_omS {c β e : Tm} (hψ : Tm.Psi (.Om c) β ∈ S) (heS : e ∈ S) :
    Lt (.Psi (.Om c) β) (.Om e) ↔ Le c e := by
  have hcS := G.sub hψ (subs_psi_p (mem_subs_om c))
  rcases Nat.lt_trichotomy (max 1 (lev e)) (max 1 (lev c)) with hl | hl | hl
  · constructor
    · intro h; have := lev_le_of_lt_gen h; simp only [lev] at this; exfalso; omega
    · intro h
      have hec : Lt e c := lt_of_lev_lt' (by omega)
      exact absurd hec (G.not_lt_of_le hcS heS h)
  · rw [lt_psiOm_om e c β hl]
    constructor
    · intro h; exact G.le_of_not_lt heS hcS h
    · intro h; exact G.not_lt_of_le hcS heS h
  · constructor
    · intro _; exact Or.inr (lt_of_lev_lt' (by omega))
    · intro _; exact lt_of_lev_lt' (by simp only [lev]; exact hl)

/-- `Ψ_{Ω_c}(β)` の崩壊先の添字は `Ψ_{Ω_c}(β)` 以下（`c = 0` も含めて） -/
theorem le_psiOm {c β : Tm} (hψ : Tm.Psi (.Om c) β ∈ S) : Le c (.Psi (.Om c) β) := by
  rcases (G.nf _ hψ).psi_shape with e | ⟨c', e, hs⟩ | ⟨n, p, e⟩
  · cases e; exact Or.inr (zero_lt (by intro h; cases h))
  · cases e; exact Or.inr (G.cx c β hψ hs)
  · cases e

/-- KL：`Ω` の不動点 `X` について `X < Ψ_{Ω_c}(β)` ⟺ `X < c` -/
theorem lt_OF_psiOmS {X c β : Tm} (hX : IsOF X) (hXS : X ∈ S)
    (hψ : Tm.Psi (.Om c) β ∈ S) :
    Lt X (.Psi (.Om c) β) ↔ Lt X c := by
  have hcS := G.sub hψ (subs_psi_p (mem_subs_om c))
  have hσS : Tm.Om c ∈ S := G.sub hψ (mem_subs_psi_p _ β)
  constructor
  · intro h
    exact (G.lt_OF_omS hX hXS hcS).mp (G.trans hXS hψ hσS h (lt_psiOm_om_self c β))
  · intro h
    exact G.lt_of_lt_of_le hXS hcS hψ h (G.le_psiOm hψ)


/-- `a < Ω_a` -/
theorem lt_om_selfS : ∀ a : Tm, Tm.Om a ∈ S → Lt a (.Om a) := by
  intro a
  induction a using size_induction with
  | h a ih =>
  intro hS
  have hF := G.nf _ hS
  have haS := G.sub hS (mem_subs_om a)
  have hfix := hF.om.2
  cases a with
  | zero => exact zero_lt (by intro e; cases e)
  | M m => simp [omegaFixed] at hfix
  | Xi m b => simp [omegaFixed] at hfix
  | Om e =>
    have heS := G.sub haS (mem_subs_om e)
    exact (G.lt_om_iffS heS haS).mpr (ih e (by simp only [Tm.size]; omega) haS)
  | Psi π β =>
    rcases (G.nf _ haS).psi_shape with rfl | ⟨c, rfl, -⟩ | ⟨n, p, rfl⟩
    · exact (G.lt_psiOm_omS haS haS).mpr (G.le_psiOm haS)
    · exact (G.lt_psiOm_omS haS haS).mpr (G.le_psiOm haS)
    · simp [omegaFixed, isXi] at hfix
  | plus x y =>
    have haF := G.nf _ haS
    have hxS := G.sub haS (subs_plus_l (self_mem_subs x))
    have hxa : Lt x (.plus x y) := lt_plus_leftY haF
    obtain ⟨hxF, -, hxp, -⟩ := haF.plus
    refine (lt_plus_prin_iffY haF rfl).mpr ?_
    cases x with
    | M m => exact bot_ltY rfl (by simp only [lev]; omega) rfl rfl hF
    | Om e =>
      have heS := G.sub hxS (mem_subs_om e)
      have hex := ih e (by simp only [Tm.size]; omega) hxS
      exact (G.lt_om_iffS heS haS).mpr (G.trans heS hxS haS hex hxa)
    | Xi m b => exact (G.lt_OF_omS (Or.inl ⟨m, b, rfl⟩) hxS haS).mpr hxa
    | Psi π β =>
      rcases hxF.psi_shape with rfl | ⟨c, rfl, -⟩ | ⟨n, p, rfl⟩
      · exact (G.lt_psiOm_omS hxS haS).mpr
          (Or.inr (G.lt_of_le_of_lt (G.sub hxS (subs_psi_p (mem_subs_om _))) hxS haS
            (G.le_psiOm hxS) hxa))
      · exact (G.lt_psiOm_omS hxS haS).mpr
          (Or.inr (G.lt_of_le_of_lt (G.sub hxS (subs_psi_p (mem_subs_om _))) hxS haS
            (G.le_psiOm hxS) hxa))
      · exact (G.lt_OF_omS (Or.inr ⟨n, p, β, rfl⟩) hxS haS).mpr hxa
    | zero => simp [isPrincipal] at hxp
    | plus _ _ => simp [isPrincipal] at hxp

theorem lt_plus_right : ∀ {a b : Tm}, Tm.plus a b ∈ S → Lt b (.plus a b)
  | a, b, hS => by
    have h := G.nf _ hS
    obtain ⟨-, hb, hap, hb0⟩ := h.plus
    have hbS := G.sub hS (subs_plus_r (self_mem_subs b))
    have haS := G.sub hS (subs_plus_l (self_mem_subs a))
    cases hs : summands b with
    | nil => exact absurd hs (summands_ne_nil hb0)
    | cons x xs =>
      have hxa := h.plus_head hs
      have hxm : x ∈ summands b := by rw [hs]; exact List.mem_cons_self
      have hx := summands_WNF b hb x hxm
      have hxS := G.sub hbS (mem_subs_of_mem_summands hxm)
      have hxa' : cmpP x a ≠ .gt := by rwa [← cmp_principal hx.2 hap]
      unfold Lt
      rw [cmp_eq, hs, summands_plus, hs]
      cases e : cmpP x a with
      | lt => rw [cmpList_cons_cons_ne _ _ (by rw [e]; decide), e]
      | gt => exact absurd e hxa'
      | eq =>
        rw [cmpList_cons_cons_eq _ _ e]
        have hxe : x = a := G.eq_of_cmpP_eq hxS haS hx.2 hap e
        subst hxe
        cases b with
        | zero => exact absurd rfl hb0
        | plus p q =>
          rw [summands_plus, List.cons.injEq] at hs
          obtain ⟨rfl, hq⟩ := hs
          have := lt_plus_right hbS
          unfold Lt at this
          rw [cmp_eq, summands_plus] at this
          rwa [← hq]
        | _ =>
          simp only [summands, List.cons.injEq] at hs
          rw [← hs.2]
          exact cmpList_nil_cons _ _

/-- 前線の元は項以下 -/
theorem fr_le {R : Tm} (hR : R ∈ S) : ∀ {x w : Tm}, x ∈ S → w ∈ fr R x → Le w x
  | .zero, _, _, h | .M _, _, _, h => by simp [fr] at h
  | .plus a b, w, hx, h => by
    have haS := G.sub hx (subs_plus_l (self_mem_subs a))
    have hbS := G.sub hx (subs_plus_r (self_mem_subs b))
    have hwS := G.sub hx (fr_spec h).1
    rw [fr, List.mem_append] at h
    rcases h with h | h
    · exact Or.inr (G.lt_of_le_of_lt hwS haS hx (fr_le hR haS h) (lt_plus_leftY (G.nf _ hx)))
    · exact Or.inr (G.lt_of_le_of_lt hwS hbS hx (fr_le hR hbS h) (G.lt_plus_right hx))
  | .Om a, w, hx, h => by
    have haS := G.sub hx (mem_subs_om a)
    have hwS := G.sub hx (fr_spec h).1
    rw [fr] at h
    exact Or.inr (G.lt_of_le_of_lt hwS haS hx (fr_le hR haS h) (G.lt_om_selfS a hx))
  | .Xi m a, w, hx, h => by
    have hwS := G.sub hx (fr_spec h).1
    have hwR := (fr_spec h).2
    rw [fr] at h
    by_cases hl : Lt (.Xi m a) R
    · simp only [hl, ↓reduceIte, List.mem_singleton] at h
      exact Or.inl h
    · exact Or.inr (G.lt_of_lt_of_le hwS hR hx hwR (G.le_of_not_lt hx hR hl))
  | .Psi p a, w, hx, h => by
    have hwS := G.sub hx (fr_spec h).1
    have hwR := (fr_spec h).2
    rw [fr] at h
    by_cases hl : Lt (.Psi p a) R
    · simp only [hl, ↓reduceIte, List.mem_singleton] at h
      exact Or.inl h
    · exact Or.inr (G.lt_of_lt_of_le hwS hR hx hwR (G.le_of_not_lt hx hR hl))

end GoodY

end MahloOCF

/-! ## 新しい項 `t` との反対称性 -/

namespace MahloOCF

open Tm

/-- `t` と `s` の反対称性と相等 -/
def AntiT (t s : Tm) : Prop := cmp s t = (cmp t s).swap ∧ (cmp t s = .eq → t = s)

theorem swap_eq_eq {o : Ordering} (h : o.swap = .eq) : o = .eq := by
  cases o <;> first | rfl | cases h

/-- `Ω_X`（`X` は `Ω` の不動点）は標準形でない -/
theorem not_WNF_om_OF {X : Tm} (hX : IsOF X) (h : WNF (.Om X)) : False := by
  have := h.om.2
  rw [hX.fixed] at this
  cases this

theorem not_WNF_om_M {m : Nat} (h : WNF (.Om (.M m))) : False := by
  have := h.om.2
  simp [omegaFixed] at this

/-- `cmpPsi` の反対称性：崩壊先どうしと引数どうしの反対称性から -/
theorem cmpPsi_swap {π γ σ β : Tm}
    (hπσ : cmp σ π = (cmp π σ).swap ∧ (cmp π σ = .eq → π = σ))
    (hγβ : cmp β γ = (cmp γ β).swap) :
    cmpPsi (.Psi σ β) (.Psi π γ) = (cmpPsi (.Psi π γ) (.Psi σ β)).swap := by
  rw [cmpPsi_eq, cmpPsi_eq]
  by_cases e : π = σ
  · subst e
    simp only [↓reduceIte]
    exact hγβ
  · have e' : σ ≠ π := fun h => e h.symm
    simp only [e, e', ↓reduceIte]
    cases h1 : cmp π σ with
    | eq => exact absurd (hπσ.2 h1) e
    | lt =>
      have h2 : cmp σ π = .gt := by rw [hπσ.1, h1]; rfl
      simp only [h2, reduceCtorEq, ↓reduceIte]
      cases baseOf π (Tm.Psi σ β) <;> rfl
    | gt =>
      have h2 : cmp σ π = .lt := by rw [hπσ.1, h1]; rfl
      simp only [h2, reduceCtorEq, ↓reduceIte]
      cases baseOf σ (Tm.Psi π γ) <;> rfl

/-- `cmpPsi` が `.eq` なら崩壊先が等しく引数の `cmp` が `.eq` -/
theorem cmpPsi_eq_eq {π γ σ β : Tm} (h : cmpPsi (.Psi π γ) (.Psi σ β) = .eq) :
    π = σ ∧ cmp γ β = .eq := by
  rw [cmpPsi_eq] at h
  by_cases e : π = σ
  · simp only [e, ↓reduceIte] at h
    exact ⟨e, h⟩
  · simp only [e, ↓reduceIte] at h
    split at h
    · split at h <;> cases h
    · split at h <;> cases h

theorem cmpP_M_xi {m n : Nat} {b : Tm} (hl : m + 1 = n) :
    cmpP (.M m) (.Xi n b) = .lt ∧ cmpP (.Xi n b) (.M m) = .gt := by
  subst hl
  constructor <;> (rw [cmpP.eq_def]; simp [lev])

theorem cmpP_M_psi {m : Nat} {π β : Tm} (hl : m + 1 = lev π) :
    cmpP (.M m) (.Psi π β) = .lt ∧ cmpP (.Psi π β) (.M m) = .gt := by
  constructor <;> (rw [cmpP.eq_def]; simp [lev, ← hl])

theorem cmpP_M_om {m : Nat} {b : Tm} (hl : m + 1 = max 1 (lev b)) :
    cmpP (.M m) (.Om b) = (if b = .M m then .eq else .lt) ∧
      cmpP (.Om b) (.M m) = (if b = .M m then .eq else .gt) := by
  constructor <;> (rw [cmpP.eq_def]; simp [lev, ← hl])

namespace GoodY

variable {S : List Tm} (G : GoodY S)
include G

/-- 同じ階の主要項どうしの、新しい項 `t` との `cmpP` は `.eq` にならない -/
theorem eqP_new {t y : Tm} (ht : WNF t) (hsub : ∀ s, s ∈ subs t → s ≠ t → s ∈ S)
    (hy : y ∈ S) (hne : y ≠ t) (htp : isPrincipal t = true) (hyp : isPrincipal y = true)
    (ih : ∀ u, u ∈ S → u.size < y.size → cmp u t ≠ .eq) :
    cmpP t y ≠ .eq ∧ cmpP y t ≠ .eq := by
  have hyF := G.nf y hy
  by_cases h1 : lev t < lev y
  · rw [cmpP_of_lev_lt h1, cmpP_of_lev_gt h1]; exact ⟨by decide, by decide⟩
  by_cases h2 : lev y < lev t
  · rw [cmpP_of_lev_gt h2, cmpP_of_lev_lt h2]; exact ⟨by decide, by decide⟩
  have hl : lev t = lev y := by omega
  have sub1 : ∀ e, e ∈ subs t → e.size < t.size → e ∈ S := fun e he hs =>
    hsub e he (ne_of_mem_subs_lt hs)
  cases t <;> cases y
  all_goals first
    | (exfalso; simp [isPrincipal] at htp hyp; done)
    | skip
  case M.M m n =>
    have : n = m := by simp only [lev] at hl; omega
    subst this
    exact absurd rfl hne
  case M.Om m b =>
    have hb : b ≠ .M m := fun e => by subst e; exact not_WNF_om_M hyF
    obtain ⟨e1, e2⟩ := cmpP_M_om (m := m) (b := b) hl
    rw [e1, e2]
    simp [hb]
  case Om.M a m =>
    have ha : a ≠ .M m := fun e => by subst e; exact not_WNF_om_M ht
    obtain ⟨e1, e2⟩ := cmpP_M_om (m := m) (b := a) hl.symm
    rw [e1, e2]
    simp [ha]
  case M.Xi m n b =>
    obtain ⟨e1, e2⟩ := cmpP_M_xi (m := m) (n := n) (b := b) hl
    rw [e1, e2]; exact ⟨by decide, by decide⟩
  case Xi.M n b m =>
    obtain ⟨e1, e2⟩ := cmpP_M_xi (m := m) (n := n) (b := b) hl.symm
    rw [e1, e2]; exact ⟨by decide, by decide⟩
  case M.Psi m π β =>
    obtain ⟨e1, e2⟩ := cmpP_M_psi (m := m) (π := π) (β := β) hl
    rw [e1, e2]; exact ⟨by decide, by decide⟩
  case Psi.M π β m =>
    obtain ⟨e1, e2⟩ := cmpP_M_psi (m := m) (π := π) (β := β) hl.symm
    rw [e1, e2]; exact ⟨by decide, by decide⟩
  case Om.Om e a =>
    have heS := sub1 e (mem_subs_om e) (by simp only [Tm.size]; omega)
    have haS := G.sub hy (mem_subs_om a)
    have hl' : max 1 (lev e) = max 1 (lev a) := hl
    rw [cmpP_om_om hl', cmpP_om_om hl'.symm]
    refine ⟨fun h => hne ?_, fun h => hne ?_⟩
    · rw [G.eq heS haS h]
    · rw [G.eq haS heS h]
  case Om.Xi e n b =>
    have heS := sub1 e (mem_subs_om e) (by simp only [Tm.size]; omega)
    have hl' : max 1 (lev e) = n := hl
    rw [cmpP_om_xi hl', cmpP_xi_om hl']
    have key : cmp e (.Xi n b) ≠ .eq := fun h => by
      have := G.eq heS hy h
      subst this
      exact not_WNF_om_OF (Or.inl ⟨n, b, rfl⟩) ht
    exact ⟨key, fun h => key (swap_eq_eq h)⟩
  case Xi.Om n b a =>
    have haS := G.sub hy (mem_subs_om a)
    have hl' : max 1 (lev a) = n := hl.symm
    rw [cmpP_om_xi hl', cmpP_xi_om hl']
    have key := ih a haS (by simp only [Tm.size]; omega)
    exact ⟨fun h => key (swap_eq_eq h), key⟩
  case Om.Psi e κ β =>
    have heS := sub1 e (mem_subs_om e) (by simp only [Tm.size]; omega)
    rcases hyF.psi_shape with rfl | ⟨c, rfl, -⟩ | ⟨n, p, rfl⟩
    · rw [cmpP_om_psiOm hl, cmpP_psiOm_om hl]
      by_cases h : cmp e Tm.zero = .lt <;> simp [h]
    · rw [cmpP_om_psiOm hl, cmpP_psiOm_om hl]
      by_cases h : cmp e c = .lt <;> simp [h]
    · have hl' : max 1 (lev e) = n := hl
      rw [cmpP_om_psiXi hl', cmpP_psiXi_om hl']
      have key : cmp e (.Psi (.Xi n p) β) ≠ .eq := fun h => by
        have := G.eq heS hy h
        subst this
        exact not_WNF_om_OF (Or.inr ⟨n, p, β, rfl⟩) ht
      exact ⟨key, fun h => key (swap_eq_eq h)⟩
  case Psi.Om π γ a =>
    have haS := G.sub hy (mem_subs_om a)
    rcases ht.psi_shape with rfl | ⟨c, rfl, -⟩ | ⟨n, p, rfl⟩
    · rw [cmpP_om_psiOm hl.symm, cmpP_psiOm_om hl.symm]
      by_cases h : cmp a Tm.zero = .lt <;> simp [h]
    · rw [cmpP_om_psiOm hl.symm, cmpP_psiOm_om hl.symm]
      by_cases h : cmp a c = .lt <;> simp [h]
    · have hl' : max 1 (lev a) = n := hl.symm
      rw [cmpP_om_psiXi hl', cmpP_psiXi_om hl']
      have key := ih a haS (by simp only [Tm.size]; omega)
      exact ⟨fun h => key (swap_eq_eq h), key⟩
  case Xi.Xi n γ m b =>
    have : n = m := hl
    subst this
    rw [cmpP_xi_xi, cmpP_xi_xi]
    have h1 : γ ≠ b := fun e => hne (by rw [e])
    have h2 : b ≠ γ := fun e => h1 e.symm
    simp only [h1, h2, ↓reduceIte]
    exact ⟨by split <;> decide, by split <;> decide⟩
  case Psi.Xi π γ m b =>
    have hl' : lev π = m := hl
    rw [cmpP_psi_xi hl', cmpP_xi_psi hl']
    exact ⟨by split <;> decide, by split <;> decide⟩
  case Xi.Psi m b κ β =>
    have hl' : lev κ = m := hl.symm
    rw [cmpP_psi_xi hl', cmpP_xi_psi hl']
    exact ⟨by split <;> decide, by split <;> decide⟩
  case Psi.Psi π γ σ β =>
    have hl' : lev π = lev σ := hl
    have hγS := sub1 γ (mem_subs_psi_a π γ) (by simp only [Tm.size]; omega)
    have hβS := G.sub hy (mem_subs_psi_a σ β)
    rw [cmpP_psi_psi hl', cmpP_psi_psi hl'.symm]
    refine ⟨fun h => ?_, fun h => ?_⟩
    · obtain ⟨rfl, h'⟩ := cmpPsi_eq_eq h
      exact hne (by rw [G.eq hγS hβS h'])
    · obtain ⟨rfl, h'⟩ := cmpPsi_eq_eq h
      exact hne (by rw [G.eq hβS hγS h'])

/-- `S` の元と新しい項 `t` の `cmp` は `.eq` にならない -/
theorem ne_new {t : Tm} (ht : WNF t) (hsub : ∀ s, s ∈ subs t → s ≠ t → s ∈ S) (htS : t ∉ S) :
    ∀ z, z ∈ S → cmp z t ≠ .eq ∧ cmp t z ≠ .eq := by
  have key : ∀ N, ∀ z, z ∈ S → z.size ≤ N → cmp z t ≠ .eq ∧ cmp t z ≠ .eq := by
    intro N
    induction N with
    | zero => intro z _ h; exact absurd h (by have := Tm.size_pos z; omega)
    | succ N ih =>
      intro z hz hs
      have hzF := G.nf z hz
      have hP : ∀ x, x ∈ summands z → ∀ w, w ∈ summands t →
          (cmpP x w = .eq → x = w) ∧ (cmpP w x = .eq → w = x) := by
        intro x hx w hw
        have hxS := G.sub hz (mem_subs_of_mem_summands hx)
        obtain ⟨-, hxp⟩ := summands_WNF z hzF x hx
        obtain ⟨-, hwp⟩ := summands_WNF t ht w hw
        cases htp : isPrincipal t
        · have hwS : w ∈ S := hsub w (mem_subs_of_mem_summands hw) (by
            intro e; subst e; rw [hwp] at htp; cases htp)
          exact ⟨G.eq_of_cmpP_eq hxS hwS hxp hwp, G.eq_of_cmpP_eq hwS hxS hwp hxp⟩
        · rw [summands_principal htp, List.mem_singleton] at hw
          subst hw
          have hxs := size_le_of_mem_summands z x hx
          have := G.eqP_new ht hsub hxS (fun e => htS (e ▸ hxS)) htp hxp
            (fun u hu hus => (ih u hu (by omega)).1)
          exact ⟨fun h => absurd h this.2, fun h => absurd h this.1⟩
      refine ⟨fun h => ?_, fun h => ?_⟩
      · rw [cmp_eq] at h
        have := eq_of_summands_eq hzF ht
          (eq_of_cmpList_eq _ _ (fun x hx w hw => (hP x hx w hw).1) h)
        exact htS (this ▸ hz)
      · rw [cmp_eq] at h
        have := eq_of_summands_eq ht hzF
          (eq_of_cmpList_eq _ _ (fun w hw x hx => (hP x hx w hw).2) h)
        exact htS (this ▸ hz)
  exact fun z hz => key _ z hz (Nat.le_refl _)

/-- `S` の元 `z` が `cmp z t ≠ .gt` なら `z < t` -/
theorem lt_of_ne_gt_new {t z : Tm} (ht : WNF t) (hsub : ∀ s, s ∈ subs t → s ≠ t → s ∈ S)
    (htS : t ∉ S) (hz : z ∈ S) (h : cmp z t ≠ .gt) : Lt z t := by
  have := (G.ne_new ht hsub htS z hz).1
  unfold Lt
  cases e : cmp z t
  · rfl
  · exact absurd e this
  · exact absurd e h

/-- 同じ階の主要項どうしの、新しい項 `t` との反対称性 -/
theorem swapP_new {t y : Tm} (ht : WNF t) (hsub : ∀ s, s ∈ subs t → s ≠ t → s ∈ S)
    (hy : y ∈ S) (htp : isPrincipal t = true) (hyp : isPrincipal y = true) :
    cmpP y t = (cmpP t y).swap := by
  have hyF := G.nf y hy
  by_cases h1 : lev t < lev y
  · rw [cmpP_of_lev_lt h1, cmpP_of_lev_gt h1]; rfl
  by_cases h2 : lev y < lev t
  · rw [cmpP_of_lev_gt h2, cmpP_of_lev_lt h2]; rfl
  have hl : lev t = lev y := by omega
  have sub1 : ∀ e, e ∈ subs t → e.size < t.size → e ∈ S := fun e he hs =>
    hsub e he (ne_of_mem_subs_lt hs)
  cases t <;> cases y
  all_goals first
    | (exfalso; simp [isPrincipal] at htp hyp; done)
    | skip
  case M.M m n =>
    have : n = m := by simp only [lev] at hl; omega
    subst this
    rw [cmpP_self]; rfl
  case M.Om m b =>
    obtain ⟨e1, e2⟩ := cmpP_M_om (m := m) (b := b) hl
    rw [e1, e2]
    by_cases hb : b = .M m <;> simp [hb]
  case Om.M a m =>
    obtain ⟨e1, e2⟩ := cmpP_M_om (m := m) (b := a) hl.symm
    rw [e1, e2]
    by_cases hb : a = .M m <;> simp [hb]
  case M.Xi m n b =>
    obtain ⟨e1, e2⟩ := cmpP_M_xi (m := m) (n := n) (b := b) hl
    rw [e1, e2]; rfl
  case Xi.M n b m =>
    obtain ⟨e1, e2⟩ := cmpP_M_xi (m := m) (n := n) (b := b) hl.symm
    rw [e1, e2]; rfl
  case M.Psi m π β =>
    obtain ⟨e1, e2⟩ := cmpP_M_psi (m := m) (π := π) (β := β) hl
    rw [e1, e2]; rfl
  case Psi.M π β m =>
    obtain ⟨e1, e2⟩ := cmpP_M_psi (m := m) (π := π) (β := β) hl.symm
    rw [e1, e2]; rfl
  case Om.Om e a =>
    have heS := sub1 e (mem_subs_om e) (by simp only [Tm.size]; omega)
    have haS := G.sub hy (mem_subs_om a)
    have hl' : max 1 (lev e) = max 1 (lev a) := hl
    rw [cmpP_om_om hl', cmpP_om_om hl'.symm]
    exact G.swap heS haS
  case Om.Xi e n b =>
    have hl' : max 1 (lev e) = n := hl
    rw [cmpP_om_xi hl', cmpP_xi_om hl']
  case Xi.Om n b a =>
    have hl' : max 1 (lev a) = n := hl.symm
    rw [cmpP_om_xi hl', cmpP_xi_om hl', Ordering.swap_swap]
  case Om.Psi e κ β =>
    rcases hyF.psi_shape with rfl | ⟨c, rfl, -⟩ | ⟨n, p, rfl⟩
    · rw [cmpP_om_psiOm hl, cmpP_psiOm_om hl]
    · rw [cmpP_om_psiOm hl, cmpP_psiOm_om hl]
    · have hl' : max 1 (lev e) = n := hl
      rw [cmpP_om_psiXi hl', cmpP_psiXi_om hl']
  case Psi.Om π γ a =>
    rcases ht.psi_shape with rfl | ⟨c, rfl, -⟩ | ⟨n, p, rfl⟩
    · rw [cmpP_om_psiOm hl.symm, cmpP_psiOm_om hl.symm, Ordering.swap_swap]
    · rw [cmpP_om_psiOm hl.symm, cmpP_psiOm_om hl.symm, Ordering.swap_swap]
    · have hl' : max 1 (lev a) = n := hl.symm
      rw [cmpP_om_psiXi hl', cmpP_psiXi_om hl', Ordering.swap_swap]
  case Xi.Xi n γ m b =>
    have : n = m := hl
    subst this
    have hγS := sub1 γ (mem_subs_xi n γ) (by simp only [Tm.size]; omega)
    have hbS := G.sub hy (mem_subs_xi n b)
    exact (xi_SE (G.anti γ hγS b hbS)).1
  case Psi.Xi π γ m b =>
    have hl' : lev π = m := hl
    rw [cmpP_psi_xi hl', cmpP_xi_psi hl']
    split <;> rfl
  case Xi.Psi m b κ β =>
    have hl' : lev κ = m := hl.symm
    rw [cmpP_psi_xi hl', cmpP_xi_psi hl']
    split <;> rfl
  case Psi.Psi π γ σ β =>
    have hl' : lev π = lev σ := hl
    have hπS := sub1 π (mem_subs_psi_p π γ) (by simp only [Tm.size]; omega)
    have hγS := sub1 γ (mem_subs_psi_a π γ) (by simp only [Tm.size]; omega)
    have hσS := G.sub hy (mem_subs_psi_p σ β)
    have hβS := G.sub hy (mem_subs_psi_a σ β)
    rw [cmpP_psi_psi hl', cmpP_psi_psi hl'.symm]
    exact cmpPsi_swap (G.anti π hπS σ hσS) (G.swap hγS hβS)

/-- 新しい項 `t` は `S` の元と反対称 -/
theorem anti_new {t : Tm} (ht : WNF t) (hsub : ∀ s, s ∈ subs t → s ≠ t → s ∈ S)
    (htS : t ∉ S) : ∀ z, z ∈ S → AntiT t z := by
  intro z hz
  have hzF := G.nf z hz
  refine ⟨?_, fun h => absurd h (G.ne_new ht hsub htS z hz).2⟩
  rw [cmp_eq z t, cmp_eq t z]
  apply cmpList_swap
  intro x hx y hy
  have hyS := G.sub hz (mem_subs_of_mem_summands hy)
  obtain ⟨-, hyp⟩ := summands_WNF z hzF y hy
  obtain ⟨-, hxp⟩ := summands_WNF t ht x hx
  cases htp : isPrincipal t
  · have hxS : x ∈ S := hsub x (mem_subs_of_mem_summands hx) (by
      intro e; subst e; rw [hxp] at htp; cases htp)
    rw [← cmp_principal hyp hxp, ← cmp_principal hxp hyp]
    exact G.swap hxS hyS
  · rw [summands_principal htp, List.mem_singleton] at hx
    subst hx
    exact G.swapP_new ht hsub hyS htp hyp

end GoodY

/-! ### 反対称性と切断性から推移性へ -/

theorem AntiOn.asymm {S : List Tm} (hA : AntiOn S) {a b : Tm} (ha : a ∈ S) (hb : b ∈ S)
    (h : Lt a b) : ¬ Lt b a := by
  unfold Lt at *
  rw [(hA a ha b hb).1, h]
  decide

theorem AntiOn.tri {S : List Tm} (hA : AntiOn S) {a b : Tm} (ha : a ∈ S) (hb : b ∈ S) :
    Lt a b ∨ a = b ∨ Lt b a := by
  cases e : cmp a b with
  | lt => exact Or.inl e
  | eq => exact Or.inr (Or.inl ((hA a ha b hb).2 e))
  | gt =>
    refine Or.inr (Or.inr ?_)
    unfold Lt
    rw [(hA a ha b hb).1, e]
    rfl

theorem linOn_of_cutY {S S' : List Tm} {t : Tm} (hA : AntiOn S) (hLin : LinOn S')
    (inS' : ∀ s, s ∈ S → s ≠ t → s ∈ S') (cut : CutT S' t) : LinOn S := by
  intro a ha b hb c hc hab hbc
  by_cases eat : a = t <;> by_cases ebt : b = t <;> by_cases ect : c = t
  · subst eat; subst ebt; exact absurd hab (Lt.irrefl _)
  · subst eat; subst ebt; exact absurd hab (Lt.irrefl _)
  · subst eat; subst ect; exact absurd hbc (hA.asymm ha hb hab)
  · subst eat
    rcases hA.tri ha hc with h | h | h
    · exact h
    · exact absurd h.symm ect
    · exact absurd hab (hA.asymm hb ha (cut c b (inS' c hc ect) (inS' b hb ebt) hbc h))
  · subst ebt; subst ect; exact absurd hbc (Lt.irrefl _)
  · subst ebt
    rcases hA.tri ha hc with h | h | h
    · exact h
    · subst h; exact absurd hbc (hA.asymm ha hb hab)
    · exact absurd hbc (hA.asymm hc hb (cut a c (inS' a ha eat) (inS' c hc ect) h hab))
  · subst ect
    exact cut b a (inS' b hb ebt) (inS' a ha eat) hab hbc
  · exact hLin a (inS' a ha eat) b (inS' b hb ebt) c (inS' c hc ect) hab hbc

/-- `S'` が反対称で、`t` が `S'` の全ての元と反対称なら、`S' ∪ {t}` は反対称 -/
theorem antiOn_extend {S S' : List Tm} {t : Tm} (hA : AntiOn S')
    (inS' : ∀ s, s ∈ S → s ≠ t → s ∈ S') (hT : ∀ z, z ∈ S' → AntiT t z) : AntiOn S := by
  intro a ha b hb
  by_cases ea : a = t <;> by_cases eb : b = t
  · subst ea; subst eb
    rw [cmp_self]
    exact ⟨rfl, fun _ => rfl⟩
  · subst ea
    exact hT b (inS' b hb eb)
  · subst eb
    obtain ⟨h1, -⟩ := hT a (inS' a ha ea)
    refine ⟨by rw [h1, Ordering.swap_swap], fun e => ?_⟩
    have := (hT a (inS' a ha ea)).2
    rw [h1] at e
    exact (this (swap_eq_eq e)).symm
  · exact hA a (inS' a ha ea) b (inS' b hb eb)

theorem GoodY.nil : GoodY [] :=
  ⟨fun _ h => absurd h List.not_mem_nil, fun _ h => absurd h List.not_mem_nil,
    fun _ h => absurd h List.not_mem_nil, fun _ h => absurd h List.not_mem_nil,
    fun _ _ h => absurd h List.not_mem_nil, fun _ _ h => absurd h List.not_mem_nil,
    fun _ _ h => absurd h List.not_mem_nil, fun _ _ h => absurd h List.not_mem_nil⟩

end MahloOCF

/-! ## 崩壊先 `Ω_c` の底の条件の言い換えと、新しい項が `t = Ω_e` の場合 -/

namespace MahloOCF

open Tm

/-- `Ω_y < Ψ_{Ω_d}(β)` ⟺ `y < d`（階によらず） -/
theorem lt_om_psiOmG {y d β : Tm} : Lt (.Om y) (.Psi (.Om d) β) ↔ Lt y d := by
  rcases Nat.lt_trichotomy (max 1 (lev y)) (max 1 (lev d)) with hl | hl | hl
  · exact ⟨fun _ => lt_of_lev_lt' (by omega), fun _ => lt_of_lev_lt' (by simp only [lev]; exact hl)⟩
  · exact lt_om_psiOm y d β hl
  · constructor
    · intro h; have := lev_le_of_lt_gen h; simp only [lev] at this; exfalso; omega
    · intro h; have := lev_le_of_lt_gen h; exfalso; omega

/-- `Ω_a < Ω_b` ⟺ `a < b`（階によらず） -/
theorem lt_om_iffG {a b : Tm} : Lt (.Om a) (.Om b) ↔ Lt a b := by
  rcases Nat.lt_trichotomy (max 1 (lev a)) (max 1 (lev b)) with h | h | h
  · constructor
    · intro _; exact lt_of_lev_lt' (by omega)
    · intro _
      rw [lt_principal_iff rfl rfl, cmpP_of_lev_lt (by simp only [lev]; exact h)]
  · rw [lt_principal_iff rfl rfl, cmpP_om_om h]; rfl
  · constructor
    · intro h'
      rw [lt_principal_iff rfl rfl, cmpP_of_lev_gt (by simp only [lev]; exact h)] at h'
      cases h'
    · intro h'; have := lev_le_of_lt_gen h'; exfalso; omega

/-- 階が大きければ `cmp` は `.gt` -/
theorem cmp_gt_of_lev_gt {a b : Tm} (h : lev b < lev a) : cmp a b = .gt := by
  have ha0 : a ≠ .zero := by intro e; subst e; simp only [lev] at h; omega
  by_cases hb0 : b = .zero
  · subst hb0
    rw [cmp_eq]
    cases hs : summands a with
    | nil => exact absurd hs (summands_ne_nil ha0)
    | cons _ _ => exact cmpList_cons_nil _ _
  · cases hsa : summands a with
    | nil => exact absurd hsa (summands_ne_nil ha0)
    | cons x xs =>
      cases hsb : summands b with
      | nil => exact absurd hsb (summands_ne_nil hb0)
      | cons y ys =>
        rw [cmp_eq, hsa, hsb]
        have e : cmpP x y = .gt := cmpP_of_lev_gt (by rw [lev_head hsa, lev_head hsb]; exact h)
        rw [cmpList_cons_cons_ne _ _ (by rw [e]; decide), e]

theorem lev_le_of_cmp_ne_gt {a b : Tm} (h : cmp a b ≠ .gt) : lev a ≤ lev b :=
  Nat.le_of_not_lt (fun hl => h (cmp_gt_of_lev_gt hl))

/-- `Ω` の不動点の形 -/
theorem fixed_shape {z : Tm} (hz : WNF z) (hfix : omegaFixed z = true) :
    (∃ m, z = .M m) ∨ IsOF z := by
  cases z with
  | M m => exact Or.inl ⟨m, rfl⟩
  | Xi n b => exact Or.inr (Or.inl ⟨n, b, rfl⟩)
  | Psi π b =>
    rcases hz.psi_shape with rfl | ⟨c, rfl, -⟩ | ⟨n, p, rfl⟩
    · simp [omegaFixed, isXi] at hfix
    · simp [omegaFixed, isXi] at hfix
    · exact Or.inr (Or.inr ⟨n, p, b, rfl⟩)
  | _ => simp [omegaFixed] at hfix

theorem fixed_principal {z : Tm} (hfix : omegaFixed z = true) : isPrincipal z = true := by
  cases z <;> simp_all [omegaFixed, isPrincipal]

theorem IsOF.ne_one {X : Tm} (h : IsOF X) : X ≠ one := by
  rcases h with ⟨n, a, rfl⟩ | ⟨n, p, β, rfl⟩ <;> intro e <;> cases e

/-- `Ω` の不動点 `X` について：崩壊先 `Ω_c` の底の条件 `Base_{Ω_c}(X)` ⟺ `c < X` -/
theorem baseOf_om_OF {c X : Tm} (hc : WNF c) (hs : isSucc c = true) (hX : IsOF X) (hXF : WNF X) :
    baseOf (.Om c) X = true ↔ Lt c X := by
  rw [baseOf_om_succ hs, lt_succ_prin_iff hc hs hX.principal hX.ne_one hXF]
  unfold omOf
  split
  · exact Iff.rfl
  · exact lt_om_OFG hX hXF

/-- 崩壊先 `Ω_c`、`c ≤ d` なら `Base_{Ω_c}(Ψ_{Ω_d}(β))`（`Ω` の不動点 `X < d` が `X < Ψ_{Ω_d}(β)` を
    満たすことを仮定する） -/
theorem baseOf_om_psiOm {c d β : Tm} (hc : WNF c) (hs : isSucc c = true) (hψF : WNF (.Psi (.Om d) β))
    (hcd : cmp c d ≠ .gt)
    (hKL : ∀ X, IsOF X → X ∈ summands c → Lt X d → Lt X (.Psi (.Om d) β)) :
    baseOf (.Om c) (.Psi (.Om d) β) = true := by
  rw [baseOf_om_succ hs]
  have hζd : Lt (predT c) d := (lt_predT_iff hc hs (hψF.psi.piF.om.1)).mpr hcd
  unfold omOf
  split
  · rename_i hfix
    have hζF := predT_WNF hc hs
    rcases fixed_shape hζF hfix with ⟨m, hm⟩ | hX
    · rw [hm]
      obtain ⟨ys, hys⟩ := summands_of_isSucc hs
      have h1 := summands_predT hc hys
      rw [hm] at h1
      have hys' : ys = [.M m] := h1.symm
      subst hys'
      have hlc : lev (.M m) = lev c := lev_head (rest := [one]) hys
      have hle : lev c ≤ lev d := lev_le_of_cmp_ne_gt hcd
      exact bot_ltY rfl (by simp only [lev] at hlc ⊢; omega) rfl rfl hψF
    · exact hKL _ hX (predT_mem_summands hc hs (fixed_principal hfix)) hζd
  · exact lt_om_psiOmG.mpr hζd

end MahloOCF

namespace MahloOCF

open Tm

namespace GoodY

variable {S : List Tm} (G : GoodY S)
include G

/-- `Ψ_{Ω_d}(α) < X`（`X` は `Ω` の不動点）なら `d ≤ X` -/
theorem le_of_psiOm_lt_OF {d α X : Tm} (hψ : Tm.Psi (.Om d) α ∈ S) (hX : IsOF X)
    (hXS : X ∈ S) (h : Lt (.Psi (.Om d) α) X) : Le d X := by
  have hdS := G.sub hψ (subs_psi_p (mem_subs_om d))
  rcases G.tri hdS hXS with h' | h' | h'
  · exact Or.inr h'
  · exact Or.inl h'
  · exact absurd ((G.lt_OF_psiOmS hX hXS hψ).mpr h') (G.asymm hψ hXS h)

/-- `S` の中の崩壊先 `Ω_c` の底の条件：`c ≤ d` なら `Base_{Ω_c}(Ψ_{Ω_d}(β))` -/
theorem baseOf_om_psiOmS {c c' d β : Tm} (hq : Tm.Psi (.Om c) c' ∈ S)
    (hψ : Tm.Psi (.Om d) β ∈ S) (hcd : cmp c d ≠ .gt) :
    baseOf (.Om c) (.Psi (.Om d) β) = true := by
  have hcS := G.sub hq (subs_psi_p (mem_subs_om c))
  rcases (G.nf _ hq).psi_shape with e | ⟨c₀, e, hs⟩ | ⟨n, p, e⟩
  · cases e; exact (baseOf_om_zero _).mpr (by intro h; cases h)
  · cases e
    exact baseOf_om_psiOm (G.nf _ hcS) hs (G.nf _ hψ) hcd (fun X hX hXm hXd =>
      (G.lt_OF_psiOmS hX (G.sub hcS (mem_subs_of_mem_summands hXm)) hψ).mpr hXd)
  · cases e

/-- 崩壊先の添字が小さい `Ψ_{Ω_d}` は小さい -/
theorem lt_psiOm_psiOm_of_lt {d d' α β : Tm} (hq : Tm.Psi (.Om d') β ∈ S)
    (hp : Tm.Psi (.Om d) α ∈ S) (h : Lt d' d) :
    Lt (.Psi (.Om d') β) (.Psi (.Om d) α) := by
  have hdS := G.sub hp (subs_psi_p (mem_subs_om d))
  have hd'S := G.sub hq (subs_psi_p (mem_subs_om d'))
  have hOS := G.sub hp (mem_subs_psi_p _ α)
  have hO'S := G.sub hq (mem_subs_psi_p _ β)
  have hl := lev_le_of_lt_gen h
  rcases Nat.lt_or_eq_of_le (show max 1 (lev d') ≤ max 1 (lev d) by omega) with hl' | hl'
  · exact lt_of_lev_lt' (by simp only [lev]; exact hl')
  · have hO : Lt (.Om d') (.Om d) := lt_om_iffG.mpr h
    refine (lt_psi_psiY (π := .Om d') (σ := .Om d) (by simp only [lev]; exact hl')).mpr
      (Or.inr (Or.inr ⟨fun e => Lt.ne hO e, G.asymm hO'S hOS hO, ?_⟩))
    exact G.baseOf_om_psiOmS hq hp (ne_gt_of_le (Or.inr h))

/-- `Ψ_{Ω_d}(α) < Ψ_{Ω_e}(β)` なら `d ≤ e` -/
theorem le_of_lt_psiOm_psiOm {d e α β : Tm} (hx : Tm.Psi (.Om d) α ∈ S)
    (hy : Tm.Psi (.Om e) β ∈ S) (h : Lt (.Psi (.Om d) α) (.Psi (.Om e) β)) : Le d e := by
  have hd := G.sub hx (subs_psi_p (mem_subs_om d))
  have he := G.sub hy (subs_psi_p (mem_subs_om e))
  rcases G.tri hd he with h' | h' | h'
  · exact Or.inr h'
  · exact Or.inl h'
  · exact absurd (G.lt_psiOm_psiOm_of_lt hy hx h') (G.asymm hx hy h)

end GoodY

/-- `t = Ω_e` は `S` を切断する -/
theorem cut_omY {S : List Tm} (G : GoodY S) {e : Tm} (ht : WNF (.Om e))
    (hsub : ∀ s, s ∈ subs (.Om e) → s ≠ .Om e → s ∈ S) : CutT S (.Om e) := by
  have heS : e ∈ S := hsub e (mem_subs_om e) (ne_of_mem_subs_lt (by simp only [Tm.size]; omega))
  refine G.cut_of_principal ht hsub (fun _ _ _ q p hqS hpS hqp hpp _ h1 h2 => ?_)
  have hqF := G.nf q hqS
  have hpF := G.nf p hpS
  refine cut_reduceY ht rfl rfl hqF hpF hqp hpp h1 h2 (fun _ _ bq bp => ?_)
  rcases shape_prinOF hpF hpp bp with ⟨x, rfl⟩ | hpX | ⟨d, β, rfl⟩ <;>
    rcases shape_prinOF hqF hqp bq with ⟨y, rfl⟩ | hqX | ⟨d', α, rfl⟩
  · have hx := G.sub hpS (mem_subs_om x)
    have hy := G.sub hqS (mem_subs_om y)
    exact (G.lt_om_iffS hy heS).mpr (G.trans hy hx heS ((G.lt_om_iffS hy hx).mp h1)
      ((G.lt_om_iffS hx heS).mp h2))
  · have hx := G.sub hpS (mem_subs_om x)
    exact (G.lt_OF_omS hqX hqS heS).mpr (G.trans hqS hx heS ((G.lt_OF_omS hqX hqS hx).mp h1)
      ((G.lt_om_iffS hx heS).mp h2))
  · have hx := G.sub hpS (mem_subs_om x)
    have hd' := G.sub hqS (subs_psi_p (mem_subs_om d'))
    exact (G.lt_psiOm_omS hqS heS).mpr (G.le_trans hd' hx heS ((G.lt_psiOm_omS hqS hx).mp h1)
      (Or.inr ((G.lt_om_iffS hx heS).mp h2)))
  · have hy := G.sub hqS (mem_subs_om y)
    exact (G.lt_om_iffS hy heS).mpr (G.trans hy hpS heS ((lt_om_OFG hpX hpF).mp h1)
      ((G.lt_OF_omS hpX hpS heS).mp h2))
  · exact (G.lt_OF_omS hqX hqS heS).mpr (G.trans hqS hpS heS h1 ((G.lt_OF_omS hpX hpS heS).mp h2))
  · have hd' := G.sub hqS (subs_psi_p (mem_subs_om d'))
    exact (G.lt_psiOm_omS hqS heS).mpr (G.le_trans hd' hpS heS (G.le_of_psiOm_lt_OF hqS hpX hpS h1)
      (Or.inr ((G.lt_OF_omS hpX hpS heS).mp h2)))
  · have hy := G.sub hqS (mem_subs_om y)
    have hd := G.sub hpS (subs_psi_p (mem_subs_om d))
    exact (G.lt_om_iffS hy heS).mpr (G.lt_of_lt_of_le hy hd heS (lt_om_psiOmG.mp h1)
      ((G.lt_psiOm_omS hpS heS).mp h2))
  · have hd := G.sub hpS (subs_psi_p (mem_subs_om d))
    exact (G.lt_OF_omS hqX hqS heS).mpr (G.lt_of_lt_of_le hqS hd heS
      ((G.lt_OF_psiOmS hqX hqS hpS).mp h1) ((G.lt_psiOm_omS hpS heS).mp h2))
  · have hd := G.sub hpS (subs_psi_p (mem_subs_om d))
    have hd' := G.sub hqS (subs_psi_p (mem_subs_om d'))
    exact (G.lt_psiOm_omS hqS heS).mpr (G.le_trans hd' hd heS (G.le_of_lt_psiOm_psiOm hqS hpS h1)
      ((G.lt_psiOm_omS hpS heS).mp h2))

end MahloOCF

/-! ## `Ψ` の比較の規則と崩壊の性質 -/

namespace MahloOCF

open Tm

/-- `Ξ_n(f) < Ψ_π(γ)`（同じ階）⟺ `π > Ξ_n(f)` かつ `Base_{Ξ_n(f)}(Ψ_π(γ))` -/
theorem lt_xi_psi_iff {π γ f : Tm} {n : Nat} (hl : lev π = n) :
    Lt (.Xi n f) (.Psi π γ) ↔ cmp π (.Xi n f) = .gt ∧ baseOf (.Xi n f) (.Psi π γ) = true := by
  rw [lt_xi_psiY hl, lt_psi_xiY hl]
  cases cmp π (Tm.Xi n f) <;> cases baseOf (Tm.Xi n f) (Tm.Psi π γ) <;> simp

/-- 崩壊先 `κ < π`（同じ階）なら `Ψ_κ(β) < Ψ_π(γ)` ⟺ `Base_κ(Ψ_π(γ))` -/
theorem lt_psi_psi_ltT {κ β π γ : Tm} (hl : lev κ = lev π) (hne : κ ≠ π) (hnlt : ¬ Lt π κ) :
    Lt (.Psi κ β) (.Psi π γ) ↔ baseOf κ (.Psi π γ) = true := by
  rw [lt_psi_psiY hl]
  constructor
  · rintro (⟨e, -⟩ | ⟨-, h, -⟩ | ⟨-, -, h⟩)
    · exact absurd e hne
    · exact absurd h hnlt
    · exact h
  · intro h; exact Or.inr (Or.inr ⟨hne, hnlt, h⟩)

/-- 崩壊先 `π < κ`（同じ階）なら `Ψ_κ(β) < Ψ_π(γ)` ⟺ `¬ Base_π(Ψ_κ(β))` -/
theorem lt_psi_psi_gtT {κ β π γ : Tm} (hl : lev κ = lev π) (hne : κ ≠ π) (hlt : Lt π κ) :
    Lt (.Psi κ β) (.Psi π γ) ↔ baseOf π (.Psi κ β) = false := by
  rw [lt_psi_psiY hl]
  constructor
  · rintro (⟨e, -⟩ | ⟨-, -, h⟩ | ⟨-, h, -⟩)
    · exact absurd e hne
    · exact h
    · exact absurd hlt h
  · intro h; exact Or.inr (Or.inl ⟨hne, hlt, h⟩)

theorem kTerm_lt {n : Nat} {x : Tm} (hn : 1 ≤ n) (hx : WNF x) (hxp : isPrincipal x = true)
    (hxb : isBot x = false) (hl : lev x = n) : Lt (kTerm (n - 1)) x := by
  unfold kTerm
  split
  · exact zero_lt (by intro e; subst e; simp [isPrincipal] at hxp)
  · exact bot_ltY rfl (by simp only [lev]; omega) hxp hxb hx

namespace GoodY

variable {S : List Tm} (G : GoodY S)
include G

/-- 崩壊先 `π < κ` の `Ψ_κ(β) < π` なら `¬ Base_π(Ψ_κ(β))` -/
theorem not_base_of_lt_tgt {κ β π : Tm} (hz : Tm.Psi κ β ∈ S) (hπS : π ∈ S) (hπT : IsTgt π)
    (hl : lev κ = lev π) (hπκ : Lt π κ) (h : Lt (.Psi κ β) π) :
    baseOf π (.Psi κ β) = false := by
  have hzF := G.nf _ hz
  have hκS := G.sub hz (mem_subs_psi_p κ β)
  rcases hπT with rfl | ⟨c, rfl, hs⟩ | ⟨m, δ, rfl⟩
  · exfalso
    rcases hzF.psi_shape with rfl | ⟨d, rfl, -⟩ | ⟨n, p, rfl⟩
    · exact Lt.irrefl _ hπκ
    · have := (lt_psiOm_om .zero d β hl.symm).mp h
      exact this (lt_om_iffG.mp hπκ)
    · exact not_lt_zero _ ((G.lt_OF_omS (Or.inr ⟨n, p, β, rfl⟩) hz (G.sub hπS (mem_subs_om _))).mp h)
  · have hcS := G.sub hπS (mem_subs_om c)
    rcases hzF.psi_shape with rfl | ⟨d, rfl, -⟩ | ⟨n, p, rfl⟩
    · exact absurd (lt_om_iffG.mp hπκ) (not_lt_zero c)
    · exfalso
      exact (lt_psiOm_om c d β hl.symm).mp h (lt_om_iffG.mp hπκ)
    · have hX : IsOF (.Psi (.Xi n p) β) := Or.inr ⟨n, p, β, rfl⟩
      have h1 := (G.lt_OF_omS hX hz hcS).mp h
      cases e : baseOf (Tm.Om c) (Tm.Psi (Tm.Xi n p) β)
      · rfl
      · exact absurd ((baseOf_om_OF (G.nf _ hcS) hs hX hzF).mp e) (G.asymm hz hcS h1)
  · have hgt : cmp κ (.Xi m δ) = .gt := by
      unfold Lt at hπκ; rw [G.swap hπS hκS, hπκ]; rfl
    rcases (lt_psi_xiY hl).mp h with h' | h'
    · exact absurd hgt h'
    · exact h'

/-- `Ψ_κ(β) ∈ S` は自分の崩壊先の底の条件を満たす -/
theorem base_self {κ β : Tm} (hz : Tm.Psi κ β ∈ S) : baseOf κ (.Psi κ β) = true := by
  have hzF := G.nf _ hz
  rcases hzF.psi_shape with rfl | ⟨c, rfl, hs⟩ | ⟨m, δ, rfl⟩
  · exact (baseOf_om_zero _).mpr (by intro e; cases e)
  · exact G.baseOf_om_psiOmS hz hz (by rw [cmp_self]; decide)
  · have hκS := G.sub hz (mem_subs_psi_p _ β)
    have hκF := G.nf _ hκS
    obtain ⟨hm, hδF, -, hδC⟩ := hκF.xi
    have hδS := G.sub hκS (mem_subs_xi m δ)
    refine (baseOf_xi_iff m δ _).mpr ⟨kTerm_lt hm hzF rfl rfl rfl, ?_⟩
    -- `δ ∈ C(δ, Ξ_m(δ))`、前線（`Ξ_m(δ)` について）は `Ψ` 未満
    have hδX : inC δ δ (.Xi m δ) = true :=
      inC_of_fr δ hδC (fun _ _ h => h) (fun w hw => inC_of_lt_node (fr_node hw) (G.k2x m δ hκS w hw))
    have hfr : fr (Tm.Xi m δ) (Tm.Xi m δ) = fr (Tm.Xi m δ) δ := by
      rw [fr]; simp [Lt.irrefl]
    exact inC_of_fr δ hδX (fun _ _ h => h) (fun w hw => inC_of_lt_node (fr_node hw)
      (G.k2t _ β hz w (by rw [hfr]; exact hw)))

end GoodY

end MahloOCF

namespace MahloOCF

open Tm

theorem IsTgt.OF_of_not_om {π : Tm} (h : IsTgt π) (hn : ∀ c, π ≠ .Om c) : ∃ m δ, π = .Xi m δ := by
  rcases h with rfl | ⟨c, rfl, -⟩ | ⟨m, δ, rfl⟩
  · exact absurd rfl (hn _)
  · exact absurd rfl (hn c)
  · exact ⟨m, δ, rfl⟩

namespace GoodY

variable {S : List Tm} (G : GoodY S)
include G

/-- `Ψ_π(γ)` の崩壊の性質：`π ∈ S` で `z ∈ C(γ, Ψ_π(γ))`、`z < π` なら `z < Ψ_π(γ)`。
    `π = Ω_c` のときは `Ω` の不動点 `X < c` が `X < Ψ_π(γ)` を満たすことを仮定する。
    `Ψ_π(γ)` 自身は `S` に入らなくてよい。 -/
theorem coll_psi {π γ : Tm} (ht : WNF (.Psi π γ)) (hπS : π ∈ S)
    (hKLt : ∀ c, π = .Om c → ∀ X, IsOF X → X ∈ S → Lt X c → Lt X (.Psi π γ)) :
    ∀ z, z ∈ S → inC z γ (.Psi π γ) = true → Lt z π → Lt z (.Psi π γ) := by
  have hπT := ht.psi.tgt
  have hπF := ht.psi.piF
  intro z
  induction z using size_induction with
  | h z ih =>
  intro hzS hin h
  have hzF := G.nf z hzS
  have hlz : lev z ≤ lev π := lev_le_of_lt_gen h
  cases z with
  | zero => exact zero_lt (by intro e; cases e)
  | M m => exact bot_ltY rfl hlz rfl rfl ht
  | plus a b =>
    have haS := G.sub hzS (subs_plus_l (self_mem_subs a))
    rw [inC_plus, Bool.and_eq_true] at hin
    have haπ := G.trans haS hzS hπS (lt_plus_leftY hzF) h
    exact (lt_plus_prin_iffY hzF rfl).mpr (ih a (by simp only [Tm.size]; omega) haS hin.1 haπ)
  | Om e =>
    have heS := G.sub hzS (mem_subs_om e)
    rw [inC_om] at hin
    rcases hπT with rfl | ⟨c, rfl, -⟩ | ⟨m, δ, rfl⟩
    · exact lt_om_psiOmG.mpr (lt_om_iffG.mp h)
    · exact lt_om_psiOmG.mpr (lt_om_iffG.mp h)
    · have hX : IsOF (.Xi m δ) := Or.inl ⟨m, δ, rfl⟩
      have heπ := (lt_om_OFG hX hπF).mp h
      have het := ih e (by simp only [Tm.size]; omega) heS hin heπ
      exact (lt_om_OFG (Or.inr ⟨m, δ, γ, rfl⟩) ht).mpr het
  | Xi m f =>
    rcases inC_xi_iff.mp hin with h' | ⟨hf, -⟩
    · exact h'
    rcases Nat.lt_or_eq_of_le hlz with hl | hl
    · exact lt_of_lev_lt' hl
    simp only [lev] at hl
    obtain ⟨hm, hfF, -, hfC⟩ := hzF.xi
    have hfS := G.sub hzS (mem_subs_xi m f)
    have hgt : cmp π (.Xi m f) = .gt := by unfold Lt at h; rw [G.swap hzS hπS, h]; rfl
    refine (lt_xi_psi_iff (π := π) hl.symm).mpr ⟨hgt, (baseOf_xi_iff m f _).mpr
      ⟨kTerm_lt hm ht rfl rfl hl.symm, ?_⟩⟩
    refine inC_of_fr f hfC (fun _ _ h => h) (fun w hw => inC_of_lt_node (fr_node hw) ?_)
    have hwS := G.sub hfS (fr_spec hw).1
    have hws := size_le_of_mem_subs (fr_spec hw).1
    have hwπ := G.trans hwS hzS hπS (G.k2x m f hzS w hw) h
    have hwin : inC w γ (.Psi π γ) = true :=
      fr_of_inC f (fun v _ hv => not_lt_of_not_lt_M (y := Tm.Psi π γ) hl.symm hv) hf w hw
    exact ih w (by simp only [Tm.size]; omega) hwS hwin hwπ
  | Psi κ β =>
    rcases inC_psi_iff.mp hin with h' | ⟨hκ, -, hβγ⟩
    · exact h'
    rcases Nat.lt_or_eq_of_le hlz with hl | hl
    · exact lt_of_lev_lt' hl
    simp only [lev] at hl
    have hκS := G.sub hzS (mem_subs_psi_p κ β)
    have hκF := G.nf _ hκS
    rcases G.tri hκS hπS with hκπ | rfl | hπκ
    · have hne : κ ≠ π := fun e => Lt.ne hκπ e
      refine (lt_psi_psi_ltT hl hne (G.asymm hκS hπS hκπ)).mpr ?_
      rcases hzF.psi_shape with rfl | ⟨c', rfl, hs⟩ | ⟨m, δ', rfl⟩
      · exact (baseOf_om_zero _).mpr (by intro e; cases e)
      · have hc'S := G.sub hκS (mem_subs_om c')
        have hc'F := G.nf _ hc'S
        rcases hπT with rfl | ⟨c, rfl, -⟩ | ⟨m, δ, rfl⟩
        · exact absurd (lt_om_iffG.mp hκπ) (not_lt_zero c')
        · have hc'c := lt_om_iffG.mp hκπ
          exact baseOf_om_psiOm hc'F hs ht (ne_gt_of_le (Or.inr hc'c)) (fun X hX hXm hXd =>
            hKLt c rfl X hX (G.sub hc'S (mem_subs_of_mem_summands hXm)) hXd)
        · rw [inC_om] at hκ
          have hc'π := G.trans hc'S hκS hπS (G.lt_om_selfS c' hκS) hκπ
          have hc't := ih c' (by simp only [Tm.size]; omega) hc'S hκ hc'π
          exact (baseOf_om_OF hc'F hs (Or.inr ⟨m, δ, γ, rfl⟩) ht).mpr hc't
      · rcases inC_xi_iff.mp hκ with hκt | ⟨hδ', -⟩
        · exact ((lt_xi_psi_iff (π := π) (by simp only [lev] at hl; exact hl.symm)).mp hκt).2
        · obtain ⟨hm, hδF, -, hδC⟩ := hκF.xi
          have hδS := G.sub hκS (mem_subs_xi m δ')
          have hlm : lev π = m := by simp only [lev] at hl; exact hl.symm
          refine (baseOf_xi_iff m δ' _).mpr ⟨kTerm_lt hm ht rfl rfl hlm, ?_⟩
          refine inC_of_fr δ' hδC (fun _ _ h => h) (fun u hu => inC_of_lt_node (fr_node hu) ?_)
          have huS := G.sub hδS (fr_spec hu).1
          have hus := size_le_of_mem_subs (fr_spec hu).1
          have huπ := G.trans huS hκS hπS (G.k2x m δ' hκS u hu) hκπ
          have huin : inC u γ (.Psi π γ) = true :=
            fr_of_inC δ' (fun v _ hv => not_lt_of_not_lt_M (y := Tm.Psi π γ) hlm hv) hδ' u hu
          exact ih u (by simp only [Tm.size]; omega) huS huin huπ
    · exact lt_psi_psi_same.mpr hβγ
    · have hne : κ ≠ π := fun e => Lt.ne hπκ e.symm
      exact (lt_psi_psi_gtT hl hne hπκ).mpr (G.not_base_of_lt_tgt hzS hπS hπT hl hπκ h)

/-- `S` の元の崩壊 `Ψ_π(γ)` の性質 -/
theorem coll_psiS {π γ : Tm} (ht : Tm.Psi π γ ∈ S) :
    ∀ z, z ∈ S → inC z γ (.Psi π γ) = true → Lt z π → Lt z (.Psi π γ) :=
  G.coll_psi (G.nf _ ht) (G.sub ht (mem_subs_psi_p π γ)) (fun c e X hX hXS hXc => by
    subst e; exact (G.lt_OF_psiOmS hX hXS ht).mpr hXc)

end GoodY

end MahloOCF

/-! ## 新しい項が `t = Ξ_n(γ)` の場合 -/

namespace MahloOCF

open Tm

/-- 同じ階の `Ξ` どうしの比較（Lemma 4.14） -/
theorem lt_xi_xi0 {n : Nat} {a b : Tm} (hne : a ≠ b) :
    Lt (.Xi n a) (.Xi n b) ↔
      (Lt a b ∧ inC a b (.Xi n b) = true) ∨ (Lt b a ∧ inC b a (.Xi n a) = false) := by
  rw [lt_principal_iff rfl rfl, cmpP_xi_xi, xiLtXi_eq]
  unfold Lt
  simp only [hne, ↓reduceIte, ite_lt_gt_eq_lt]
  cases cmp a b <;> cases cmp b a <;> cases inC a b (Tm.Xi n b) <;> cases inC b a (Tm.Xi n a) <;>
    simp

/-- 崩壊先が `Ξ_n(γ)` 未満なら `Ψ_ρ(α) < Ξ_n(γ)` -/
theorem lt_psi_xi_of_tgt {ρ α γ : Tm} {n : Nat} (hl : lev ρ = n) (h : Lt ρ (.Xi n γ)) :
    Lt (.Psi ρ α) (.Xi n γ) :=
  (lt_psi_xiY hl).mpr (Or.inl (by unfold Lt at h; rw [h]; decide))

/-- `γ ∉ C(γ, Ψ_ρ(α))` なら `Ψ_ρ(α) < Ξ_n(γ)` -/
theorem lt_psi_xi_of_not_inC {ρ α γ : Tm} {n : Nat} (hl : lev ρ = n)
    (h : inC γ γ (.Psi ρ α) = false) : Lt (.Psi ρ α) (.Xi n γ) :=
  (lt_psi_xiY hl).mpr (Or.inr (by rw [baseOf_xi, h, Bool.and_false]))

/-- 新しい項 `t = Ξ_n(γ)` の文脈 -/
structure XiCtx (S : List Tm) (n : Nat) (γ : Tm) : Prop where
  G : GoodY S
  ht : WNF (.Xi n γ)
  hsub : ∀ s, s ∈ subs (Tm.Xi n γ) → s ≠ .Xi n γ → s ∈ S
  htS : Tm.Xi n γ ∉ S

namespace XiCtx

variable {S : List Tm} {n : Nat} {γ : Tm} (P : XiCtx S n γ)
include P

theorem γS : γ ∈ S :=
  P.hsub _ (mem_subs_xi n γ) (ne_of_mem_subs_lt (by simp only [Tm.size]; omega))

theorem hn : 1 ≤ n := P.ht.xi.1

theorem hγC : inC γ γ (.M n) = true := P.ht.xi.2.2.2

set_option linter.unusedSectionVars false in
theorem tOF : IsOF (.Xi n γ) := Or.inl ⟨n, γ, rfl⟩

theorem ne_of_mem {s : Tm} (hs : s ∈ S) : s ≠ .Xi n γ := fun e => P.htS (e ▸ hs)

theorem lt_of_ne_gt {z : Tm} (hz : z ∈ S) (h : cmp z (.Xi n γ) ≠ .gt) : Lt z (.Xi n γ) :=
  P.G.lt_of_ne_gt_new P.ht P.hsub P.htS hz h

/-- `t < z` なら `cmp z t = .gt` -/
theorem gt_of_lt {z : Tm} (hz : z ∈ S) (h : Lt (.Xi n γ) z) : cmp z (.Xi n γ) = .gt := by
  rw [(P.G.anti_new P.ht P.hsub P.htS z hz).1]
  unfold Lt at h; rw [h]; rfl

/-- `γ ∉ C(g, d)`（`γ ≤ g`）なら、`γ` の前線（`M_n` について）に `d` 未満でない元がある -/
theorem wit {g d : Tm} (hg : Le γ g) (hgS : g ∈ S) (hn' : inC γ g d = false) :
    ∃ w, w ∈ fr (.M n) γ ∧ ¬ Lt w d :=
  wit_of_not_inC P.hγC
    (fun _ hv h => P.G.lt_of_lt_of_le (P.G.sub P.γS hv) P.γS hgS h hg) hn'

/-- `S` の `Ξ_n(f)` と `t` の比較 -/
theorem lt_xi_t {f : Tm} (hX : Tm.Xi n f ∈ S) :
    Lt (.Xi n f) (.Xi n γ) ↔
      (Lt f γ ∧ inC f γ (.Xi n γ) = true) ∨ (Lt γ f ∧ inC γ f (.Xi n f) = false) :=
  lt_xi_xi0 (fun e => P.ne_of_mem hX (by rw [e]))

/-- `r < γ` で `r` の前線（`M_n` について）が `t` 未満なら `Ξ_n(r) < t` -/
theorem xi_lt_of {r : Tm} (hX : Tm.Xi n r ∈ S) (hrγ : Lt r γ)
    (hfr : ∀ u, u ∈ fr (.M n) r → Lt u (.Xi n γ)) : Lt (.Xi n r) (.Xi n γ) := by
  have G := P.G
  have hrS := G.sub hX (mem_subs_xi n r)
  exact (P.lt_xi_t hX).mpr (Or.inl ⟨hrγ, inC_of_fr r (G.nf _ hX).xi.2.2.2
    (fun v hv h => G.trans (G.sub hrS hv) hrS P.γS h hrγ)
    (fun u hu => inC_of_lt_node (fr_node hu) (hfr u hu))⟩)

/-- 補題 A の主要項の場合 -/
theorem lemA_head {h w : Tm} (hhS : h ∈ S) (hhp : isPrincipal h = true) (hlw : lev h ≤ n)
    (hw : w ∈ fr (.M n) γ) (hhw : Le h w)
    (IH : ∀ u, u ∈ S → u.size < h.size → Le u w → Lt u (.Xi n γ)) : Lt h (.Xi n γ) := by
  have G := P.G
  have hhF := G.nf _ hhS
  have hwS := G.sub P.γS (fr_spec hw).1
  rcases Nat.lt_or_eq_of_le hlw with hl | hl
  · exact lt_of_lev_lt' (by simp only [lev]; exact hl)
  by_cases hb : isBot h = true
  · exact bot_ltY hb (by simp only [lev]; omega) rfl rfl P.ht
  rcases shape_prin hhp (Bool.eq_false_iff.mpr hb) with ⟨x, rfl⟩ | ⟨m, f, rfl⟩ | ⟨ρ, δ, rfl⟩
  · have hx := G.sub hhS (mem_subs_om x)
    exact (lt_om_OFG P.tOF P.ht).mpr (IH x hx (by simp only [Tm.size]; omega)
      (Or.inr (G.lt_of_lt_of_le hx hhS hwS (G.lt_om_selfS x hhS) hhw)))
  · simp only [lev] at hl
    subst hl
    have hfS := G.sub hhS (mem_subs_xi m f)
    rcases G.tri hfS P.γS with h' | h' | h'
    · refine P.xi_lt_of hhS h' (fun u hu => ?_)
      have huS := G.sub hfS (fr_spec hu).1
      have := size_le_of_mem_subs (fr_spec hu).1
      exact IH u huS (by simp only [Tm.size]; omega)
        (Or.inr (G.lt_of_lt_of_le huS hhS hwS (G.k2x m f hhS u hu) hhw))
    · exact absurd (by rw [h']) (P.ne_of_mem hhS)
    · refine (P.lt_xi_t hhS).mpr (Or.inr ⟨h', ?_⟩)
      cases e : inC γ f (Tm.Xi m f)
      · rfl
      · exfalso
        have := fr_of_inC γ (fun w' _ hn' => not_lt_of_not_lt_M (y := Tm.Xi m f) rfl hn') e w hw
        exact G.not_lt_of_le hhS hwS hhw (coll_xi0 hhF w (G.nf _ hwS) this (fr_spec hw).2)
  · simp only [lev] at hl
    have hρS := G.sub hhS (mem_subs_psi_p ρ δ)
    have hδS := G.sub hhS (mem_subs_psi_a ρ δ)
    rcases hhF.psi_shape with rfl | ⟨c, rfl, -⟩ | ⟨m, δ', rfl⟩
    · exact lt_psi_xi_of_tgt hl ((lt_om_OFG P.tOF P.ht).mpr (zero_lt (by intro e; cases e)))
    · have hcS := G.sub hρS (mem_subs_om c)
      have hct := IH c hcS (by simp only [Tm.size]; omega)
        (G.le_trans hcS hhS hwS (G.le_psiOm hhS) hhw)
      exact lt_psi_xi_of_tgt hl ((lt_om_OFG P.tOF P.ht).mpr hct)
    · simp only [lev] at hl
      subst hl
      rcases G.tri hρS hwS with hρw | hρw | hwρ
      · exact lt_psi_xi_of_tgt rfl (IH _ hρS (by simp only [Tm.size]; omega) (Or.inr hρw))
      · exact lt_psi_xi_of_tgt rfl (IH _ hρS (by simp only [Tm.size]; omega) (Or.inl hρw))
      · rcases G.tri P.γS hδS with hγδ | hγδ | hδγ
        · -- `γ ≤ δ`：`γ ∉ C(γ, h)`
          refine lt_psi_xi_of_not_inC rfl ?_
          cases e : inC γ γ (Tm.Psi (.Xi m δ') δ)
          · rfl
          · exfalso
            have h1 := fr_of_inC γ (fun w' _ hn' => not_lt_of_not_lt_M
              (y := Tm.Psi (.Xi m δ') δ) rfl hn') e w hw
            have h2 := inC_mono w γ _ δ _ h1 (fun _ _ h => h)
              (fun v hv hvγ => G.trans (G.sub hwS hv) P.γS hδS hvγ hγδ)
            exact G.not_lt_of_le hhS hwS hhw (G.coll_psiS hhS w hwS h2 hwρ)
        · subst hγδ
          refine lt_psi_xi_of_not_inC rfl ?_
          cases e : inC γ γ (Tm.Psi (.Xi m δ') γ)
          · rfl
          · exfalso
            have h1 := fr_of_inC γ (fun w' _ hn' => not_lt_of_not_lt_M
              (y := Tm.Psi (.Xi m δ') γ) rfl hn') e w hw
            exact G.not_lt_of_le hhS hwS hhw (G.coll_psiS hhS w hwS h1 hwρ)
        · -- `δ < γ`：`ρ = Ξ_m(δ') < t`
          refine lt_psi_xi_of_tgt rfl (P.lt_of_ne_gt hρS (fun hgt => ?_))
          have htρ : Lt (.Xi m γ) (.Xi m δ') := by
            unfold Lt; rw [(P.G.anti_new P.ht P.hsub P.htS _ hρS).1] at hgt
            cases e : cmp (Tm.Xi m γ) (Tm.Xi m δ') <;> simp_all
          have hδ'S := G.sub hρS (mem_subs_xi m δ')
          have hδ'δ : Lt δ' δ := hhF.psi.act m δ' rfl
          have hδ'γ := G.trans hδ'S hδS P.γS hδ'δ hδγ
          rcases (lt_xi_xi0 (fun e => by subst e; exact Lt.irrefl _ hδ'γ)).mp htρ with
            ⟨hγδ', -⟩ | ⟨-, hn'⟩
          · exact G.asymm hδ'S P.γS hδ'γ hγδ'
          · have hρF := G.nf _ hρS
            obtain ⟨u, hu, hnu⟩ := wit_of_not_inC hρF.xi.2.2.2
              (fun v hv h => G.trans (G.sub hδ'S hv) hδ'S P.γS h hδ'γ) hn'
            have huS := G.sub hδ'S (fr_spec hu).1
            have hus := size_le_of_mem_subs (fr_spec hu).1
            have hbase := ((baseOf_xi_iff m δ' _).mp (G.base_self hhS)).2
            have h1 := fr_of_inC δ' (fun w' _ hn' => not_lt_of_not_lt_M
              (y := Tm.Psi (.Xi m δ') δ) rfl hn') hbase u hu
            have h2 := inC_mono u δ' _ δ _ h1 (fun _ _ h => h)
              (fun v hv hvδ => G.trans (G.sub huS hv) hδ'S hδS hvδ hδ'δ)
            have huh := G.coll_psiS hhS u huS h2 (G.k2x m δ' hρS u hu)
            exact hnu (IH u huS (by simp only [Tm.size]; omega)
              (Or.inr (G.lt_of_lt_of_le huS hhS hwS huh hhw)))

/-- 補題 A：`γ` の前線のどれか以下の `S` の元は `t` 未満 -/
theorem lemA_aux : ∀ N, ∀ v, v ∈ S → v.size ≤ N →
    (∃ w, w ∈ fr (.M n) γ ∧ Le v w) → Lt v (.Xi n γ) := by
  have G := P.G
  intro N
  induction N with
  | zero => intro v _ h; exact absurd h (by have := Tm.size_pos v; omega)
  | succ N ih =>
    intro v hvS hs ⟨w, hw, hvw⟩
    have hvF := G.nf _ hvS
    have hwS := G.sub P.γS (fr_spec hw).1
    have hwF := G.nf _ hwS
    cases hsv : summands v with
    | nil =>
      have : v = .zero := by cases v <;> simp_all [summands]
      subst this
      exact zero_lt (by intro e; cases e)
    | cons h rest =>
      have hmem : h ∈ summands v := by rw [hsv]; exact List.mem_cons_self
      have hhS := G.sub hvS (mem_subs_of_mem_summands hmem)
      obtain ⟨-, hhp⟩ := summands_WNF v hvF h hmem
      have hhs := size_le_of_mem_summands v h hmem
      have hhw : Le h w := G.le_trans hhS hvS hwS (head_leY hvF hsv) hvw
      have hlw : lev h ≤ n := by
        have := (lt_M_iffY hwF P.hn).mp (fr_spec hw).2
        rcases hhw with e | e
        · rw [e]; exact this
        · exact Nat.le_trans (lev_le_of_lt_gen e) this
      have hht := P.lemA_head hhS hhp hlw hw hhw (fun u hu hus huw =>
        ih u hu (by omega) ⟨w, hw, huw⟩)
      exact lt_of_head_lt rfl hsv ((lt_principal_iff hhp rfl).mp hht)

theorem lemA {v : Tm} (hv : v ∈ S) (h : ∃ w, w ∈ fr (.M n) γ ∧ Le v w) : Lt v (.Xi n γ) :=
  P.lemA_aux _ v hv (Nat.le_refl _) h

/-- K2X：`γ` の前線は全て `t` 未満 -/
theorem k2x : ∀ w, w ∈ fr (.M n) γ → Lt w (.Xi n γ) := fun w hw =>
  P.lemA (P.G.sub P.γS (fr_spec hw).1) ⟨w, hw, Le.refl _⟩

/-- `t = Ξ_n(γ)` は `S` を切断する -/
theorem cut : CutT S (.Xi n γ) := by
  have G := P.G
  refine G.cut_of_principal P.ht P.hsub (fun N ih _ q p hqS hpS hqp hpp hN h1 h2 => ?_)
  have hqF := G.nf q hqS
  have hpF := G.nf p hpS
  refine cut_reduceY P.ht rfl rfl hqF hpF hqp hpp h1 h2 (fun lq lp bq bp => ?_)
  -- 前線の証人があれば補題 A
  have viaW : ∀ w, w ∈ fr (.M n) γ → ¬ Lt w p → Lt q (.Xi n γ) := fun w hw hwn => by
    have hwS := G.sub P.γS (fr_spec hw).1
    exact P.lemA hqS ⟨w, hw, Or.inr (G.lt_of_lt_of_le hqS hpS hwS h1 (G.le_of_not_lt hwS hpS hwn))⟩
  -- `w < t` で `q ≤ w` なら `q < t`
  have viaLe : ∀ w, w ∈ S → w.size < p.size → Lt w (.Xi n γ) → Le q w → Lt q (.Xi n γ) :=
    fun w hwS hws hwt hqw => by
      rcases hqw with e | e
      · rw [e]; exact hwt
      · exact ih w q hwS hqS (by omega) e hwt
  rcases shape_prin hpp bp with ⟨x, rfl⟩ | ⟨m, f, rfl⟩ | ⟨ρ, δ, rfl⟩
  · -- `p = Ω_x`：`x < t`
    have hx := G.sub hpS (mem_subs_om x)
    have hxt : Lt x (.Xi n γ) := (lt_om_OFG P.tOF P.ht).mp h2
    rcases shape_prinOF hqF hqp bq with ⟨y, rfl⟩ | hqX | ⟨d, α, rfl⟩
    · have hy := G.sub hqS (mem_subs_om y)
      exact (lt_om_OFG P.tOF P.ht).mpr (ih x y hx hy (by simp only [Tm.size] at hN ⊢; omega)
        ((G.lt_om_iffS hy hx).mp h1) hxt)
    · exact ih x _ hx hqS (by simp only [Tm.size] at hN ⊢; omega)
        ((G.lt_OF_omS hqX hqS hx).mp h1) hxt
    · have hd := G.sub hqS (subs_psi_p (mem_subs_om d))
      have hdt : Lt d (.Xi n γ) := by
        rcases (G.lt_psiOm_omS hqS hx).mp h1 with e | e
        · rw [e]; exact hxt
        · exact ih x d hx hd (by simp only [Tm.size] at hN ⊢; omega) e hxt
      exact lt_psi_xi_of_tgt (ρ := .Om d) lq ((lt_om_OFG P.tOF P.ht).mpr hdt)
  · -- `p = Ξ_m(f)`
    simp only [lev] at lp
    subst lp
    have hfS := G.sub hpS (mem_subs_xi m f)
    rcases (P.lt_xi_t hpS).mp h2 with ⟨hfγ, hinf⟩ | ⟨hγf, hn'⟩
    · -- 前線 `w` の `w < t`
      have frt : ∀ w, w ∈ fr (.M m) f → Lt w (.Xi m γ) := fun w hw => by
        have hwS := G.sub hfS (fr_spec hw).1
        exact coll_xi0 P.ht w (G.nf _ hwS)
          (fr_of_inC f (fun w' _ hn' => not_lt_of_not_lt_M rfl hn') hinf w hw) (fr_spec hw).2
      have viaF : ∀ g, g ∈ S → Le f g → inC f g q = false → Lt q (.Xi m γ) := fun g hgS hfg hn'' => by
        obtain ⟨w, hw, hwn⟩ := wit_of_not_inC hpF.xi.2.2.2
          (fun v hv h => G.lt_of_lt_of_le (G.sub hfS hv) hfS hgS h hfg) hn''
        have hwS := G.sub hfS (fr_spec hw).1
        have := size_le_of_mem_subs (fr_spec hw).1
        exact viaLe w hwS (by simp only [Tm.size]; omega) (frt w hw) (G.le_of_not_lt hwS hqS hwn)
      rcases shape_prin hqp bq with ⟨y, rfl⟩ | ⟨m', f', rfl⟩ | ⟨ρ, α, rfl⟩
      · have hy := G.sub hqS (mem_subs_om y)
        exact (lt_om_OFG P.tOF P.ht).mpr (ih _ y hpS hy (by simp only [Tm.size] at hN ⊢; omega)
          ((lt_om_OFG (Or.inl ⟨m, f, rfl⟩) hpF).mp h1) h2)
      · simp only [lev] at lq
        subst lq
        have hf'S := G.sub hqS (mem_subs_xi m' f')
        have hne : f' ≠ f := fun e => by subst e; exact Lt.irrefl _ h1
        rcases (lt_xi_xi0 hne).mp h1 with ⟨hf'f, hin⟩ | ⟨hff', hn''⟩
        · refine (P.lt_xi_t hqS).mpr (Or.inl ⟨G.trans hf'S hfS P.γS hf'f hfγ, ?_⟩)
          refine inC_mono f' f (.Xi m' f) γ (.Xi m' γ) hin (fun v hv hvp => ?_)
            (fun v hv hvf => G.trans (G.sub hf'S hv) hfS P.γS hvf hfγ)
          have := size_le_of_mem_subs hv
          exact ih _ v hpS (G.sub hf'S hv) (by simp only [Tm.size] at hN ⊢; omega) hvp h2
        · exact viaF f' hf'S (Or.inr hff') hn''
      · have hρS : ρ ∈ S := G.sub hqS (mem_subs_psi_p ρ α)
        rcases (lt_psi_xiY (π := ρ) (a := α) (b := f) (n := m) lq).mp h1 with h' | h'
        · have hρt : Lt ρ (.Xi m γ) := by
            rcases G.le_of_ne_gt hρS hpS h' with e | e
            · rw [e]; exact h2
            · have := size_le_of_mem_subs (mem_subs_psi_p ρ α)
              exact ih _ ρ hpS hρS (by simp only [Tm.size] at hN this ⊢; omega) e h2
          exact lt_psi_xi_of_tgt (ρ := ρ) (α := α) lq hρt
        · have hinq : inC f f (.Psi ρ α) = false := by
            rw [baseOf_xi] at h'
            have hk : (cmp (kTerm (m - 1)) (Tm.Psi ρ α) == .lt) = true := by
              have := kTerm_lt (n := m) P.hn hqF rfl rfl lq
              unfold Lt at this; rw [this]; rfl
            rw [hk, Bool.true_and] at h'
            exact h'
          exact viaF f hfS (Le.refl _) hinq
    · obtain ⟨w, hw, hwn⟩ := P.wit (Or.inr hγf) hfS hn'
      exact viaW w hw hwn
  · -- `p = Ψ_ρ(δ)`
    have hρS : ρ ∈ S := G.sub hpS (mem_subs_psi_p ρ δ)
    rcases (lt_psi_xiY (π := ρ) (a := δ) (b := γ) (n := n) lp).mp h2 with h' | h'
    · have hρt := P.lt_of_ne_gt hρS h'
      have := size_le_of_mem_subs (mem_subs_psi_p ρ δ)
      exact ih ρ q hρS hqS (by simp only [Tm.size] at hN this ⊢; omega)
        (G.trans hqS hpS hρS h1 (lt_psi_targetY hpF)) hρt
    · have hn' : inC γ γ (.Psi ρ δ) = false := by
        rw [baseOf_xi] at h'
        have hk : (cmp (kTerm (n - 1)) (Tm.Psi ρ δ) == .lt) = true := by
          have := kTerm_lt (n := n) P.hn hpF rfl rfl lp
          unfold Lt at this; rw [this]; rfl
        rw [hk, Bool.true_and] at h'
        exact h'
      obtain ⟨w, hw, hwn⟩ := P.wit (Le.refl _) P.γS hn'
      exact viaW w hw hwn

end XiCtx

end MahloOCF

/-! ## 新しい項が `t = Ψ_π(γ)` の場合 -/

namespace MahloOCF

open Tm

theorem fr_self_xi (n : Nat) (r : Tm) : fr (.Xi n r) (.Xi n r) = fr (.Xi n r) r := by
  rw [fr]; simp [Lt.irrefl]

theorem fr_self_om (c : Tm) : fr (.Om c) (.Om c) = fr (.Om c) c := by
  rw [fr]

namespace GoodY

variable {S : List Tm} (G : GoodY S)
include G

/-- `Ξ_m(f) ∈ S` なら `f ∈ C(f, Ξ_m(f))` -/
theorem xi_self {m : Nat} {f : Tm} (hX : Tm.Xi m f ∈ S) : inC f f (.Xi m f) = true :=
  inC_of_fr f (G.nf _ hX).xi.2.2.2 (fun _ _ h => h)
    (fun w hw => inC_of_lt_node (fr_node hw) (G.k2x m f hX w hw))

end GoodY

/-- 新しい項 `t = Ψ_π(γ)` の文脈 -/
structure PsiCtx (S : List Tm) (π γ : Tm) : Prop where
  G : GoodY S
  ht : WNF (.Psi π γ)
  hsub : ∀ s, s ∈ subs (Tm.Psi π γ) → s ≠ .Psi π γ → s ∈ S
  htS : Tm.Psi π γ ∉ S

namespace PsiCtx

variable {S : List Tm} {π γ : Tm} (P : PsiCtx S π γ)
include P

theorem πS : π ∈ S :=
  P.hsub _ (mem_subs_psi_p π γ) (ne_of_mem_subs_lt (by simp only [Tm.size]; have := Tm.size_pos γ; omega))

theorem γS : γ ∈ S :=
  P.hsub _ (mem_subs_psi_a π γ) (ne_of_mem_subs_lt (by simp only [Tm.size]; have := Tm.size_pos π; omega))

theorem hT : IsTgt π := P.ht.psi.tgt

theorem πF : WNF π := P.ht.psi.piF

theorem ne_of_mem {s : Tm} (hs : s ∈ S) : s ≠ .Psi π γ := fun e => P.htS (e ▸ hs)

theorem lt_of_ne_gt {z : Tm} (hz : z ∈ S) (h : cmp z (.Psi π γ) ≠ .gt) : Lt z (.Psi π γ) :=
  P.G.lt_of_ne_gt_new P.ht P.hsub P.htS hz h

/-- `t` との非対称性 -/
theorem asymm_t {z : Tm} (hz : z ∈ S) (h1 : Lt z (.Psi π γ)) (h2 : Lt (.Psi π γ) z) : False := by
  have := (P.G.anti_new P.ht P.hsub P.htS z hz).1
  unfold Lt at h1 h2
  rw [h2] at this
  rw [this] at h1
  cases h1

/-- `t` との三分律 -/
theorem lt_or_gt {z : Tm} (hz : z ∈ S) : Lt z (.Psi π γ) ∨ Lt (.Psi π γ) z := by
  have hne := (P.G.ne_new P.ht P.hsub P.htS z hz).1
  cases e : cmp z (.Psi π γ) with
  | lt => exact Or.inl e
  | eq => exact absurd e hne
  | gt =>
    right
    have h := (P.G.anti_new P.ht P.hsub P.htS z hz).1
    rw [e] at h
    unfold Lt
    cases hc : cmp (Tm.Psi π γ) z <;> rw [hc] at h <;> first | rfl | cases h

/-- `π` が `Ω` の不動点なら `t` も -/
theorem tOF {δ : Tm} {n : Nat} (h : π = .Xi n δ) : IsOF (.Psi π γ) := by
  subst h; exact Or.inr ⟨n, δ, γ, rfl⟩

/-- tb：`z < t` なら `z < π` -/
theorem tb : ∀ z, z ∈ S → Lt z (.Psi π γ) → Lt z π := by
  have G := P.G
  have hπS := P.πS
  have hπF := P.πF
  intro z
  induction z using size_induction with
  | h z ih =>
  intro hzS h
  have hzF := G.nf z hzS
  have hlz : lev z ≤ lev π := (lev_le_of_lt_gen h : lev z ≤ lev (Tm.Psi π γ))
  have hπ0 : π ≠ .zero := by rcases P.hT with rfl | ⟨c, rfl, -⟩ | ⟨n, p, rfl⟩ <;> intro e <;> cases e
  have hπp : isPrincipal π = true := by rcases P.hT with rfl | ⟨c, rfl, -⟩ | ⟨n, p, rfl⟩ <;> rfl
  have hπb : isBot π = false := by rcases P.hT with rfl | ⟨c, rfl, -⟩ | ⟨n, p, rfl⟩ <;> rfl
  rcases Nat.lt_or_eq_of_le hlz with hl | hl
  · exact lt_of_lev_lt' hl
  cases z with
  | zero => exact zero_lt hπ0
  | M m => exact bot_ltY rfl hlz hπp hπb hπF
  | plus a b =>
    have haS := G.sub hzS (subs_plus_l (self_mem_subs a))
    have hat := (lt_plus_prin_iffY hzF rfl).mp h
    exact (lt_plus_prin_iffY hzF hπp).mpr (ih a (by simp only [Tm.size]; omega) haS hat)
  | Om e =>
    have heS := G.sub hzS (mem_subs_om e)
    rcases P.hT with rfl | ⟨c, rfl, -⟩ | ⟨n, p, rfl⟩
    · exact lt_om_iffG.mpr (lt_om_psiOmG.mp h)
    · exact lt_om_iffG.mpr (lt_om_psiOmG.mp h)
    · have het := (lt_om_OFG (Or.inr ⟨n, p, γ, rfl⟩) P.ht).mp h
      exact (lt_om_OFG (Or.inl ⟨n, p, rfl⟩) hπF).mpr (ih e (by simp only [Tm.size]; omega) heS het)
  | Xi m f =>
    have hgt := ((lt_xi_psi_iff (π := π) (γ := γ) (f := f) (n := m) hl.symm).mp h).1
    exact G.lt_of_gt hπS hzS hgt
  | Psi κ β =>
    have hκS := G.sub hzS (mem_subs_psi_p κ β)
    rcases G.tri hκS hπS with hκπ | rfl | hπκ
    · exact G.trans hzS hκS hπS (lt_psi_targetY hzF) hκπ
    · exact lt_psi_targetY hzF
    · have hne : κ ≠ π := fun e => Lt.ne hπκ e.symm
      have hb := (lt_psi_psi_gtT (κ := κ) (β := β) hl hne hπκ).mp h
      rcases P.hT with rfl | ⟨c, rfl, hs⟩ | ⟨n, p, rfl⟩
      · rw [(baseOf_om_zero _).mpr (by intro e; cases e)] at hb; cases hb
      · have hcS := G.sub hπS (mem_subs_om c)
        have hcF := G.nf _ hcS
        rcases hzF.psi_shape with rfl | ⟨d, rfl, -⟩ | ⟨n, p, rfl⟩
        · exact absurd (lt_om_iffG.mp hπκ) (not_lt_zero c)
        · have hbt := baseOf_om_psiOm hcF hs hzF (ne_gt_of_le (Or.inr (lt_om_iffG.mp hπκ)))
            (fun X hX hXm hXd => (G.lt_OF_psiOmS hX (G.sub hcS (mem_subs_of_mem_summands hXm))
              hzS).mpr hXd)
          rw [hbt] at hb; cases hb
        · have hX : IsOF (.Psi (.Xi n p) β) := Or.inr ⟨n, p, β, rfl⟩
          have hnc : ¬ Lt c (.Psi (.Xi n p) β) := fun h' => by
            rw [(baseOf_om_OF hcF hs hX hzF).mpr h'] at hb; cases hb
          have hzc : Lt (.Psi (.Xi n p) β) c := by
            rcases G.le_of_not_lt hcS hzS hnc with e | e
            · exfalso
              have : isSucc (Tm.Psi (.Xi n p) β) = true := e ▸ hs
              simp [isSucc, summands, one] at this
            · exact e
          exact G.trans hzS hcS hπS hzc (G.lt_om_selfS c hπS)
      · exact (lt_psi_xiY (π := κ) (a := β) (b := p) (n := n) hl).mpr (Or.inr hb)

end PsiCtx

end MahloOCF

namespace MahloOCF

open Tm

namespace PsiCtx

variable {S : List Tm} {π γ : Tm} (P : PsiCtx S π γ)
include P

/-- Below：`π = Ω_c`（`c` は後者）なら、`c` 未満の `S` の元は `t` 未満 -/
theorem below {c : Tm} (hπ : π = .Om c) (_hs : isSucc c = true) :
    ∀ v, v ∈ S → Lt v c → Lt v (.Psi π γ) := by
  subst hπ
  have G := P.G
  have hπS := P.πS
  have hcS := G.sub hπS (mem_subs_om c)
  have hcF := G.nf _ hcS
  have hcπ : Lt c (.Om c) := G.lt_om_selfS c hπS
  intro v
  induction v using size_induction with
  | h v ih =>
  intro hvS h
  have hvF := G.nf v hvS
  have hvπ := G.trans hvS hcS hπS h hcπ
  have hlv : lev v ≤ lev (.Om c) := lev_le_of_lt_gen hvπ
  rcases Nat.lt_or_eq_of_le hlv with hl | hl
  · exact lt_of_lev_lt' hl
  cases v with
  | zero => exact zero_lt (by intro e; cases e)
  | M m => exact bot_ltY rfl hlv rfl rfl P.ht
  | plus a b =>
    have haS := G.sub hvS (subs_plus_l (self_mem_subs a))
    have hac := G.trans haS hvS hcS (lt_plus_leftY hvF) h
    exact (lt_plus_prin_iffY hvF rfl).mpr (ih a (by simp only [Tm.size]; omega) haS hac)
  | Om e =>
    have heS := G.sub hvS (mem_subs_om e)
    exact lt_om_psiOmG.mpr (G.trans heS hvS hcS (G.lt_om_selfS e hvS) h)
  | Xi m f =>
    have hgt : cmp (Tm.Om c) (.Xi m f) = .gt := by
      unfold Lt at hvπ; rw [G.swap hvS hπS, hvπ]; rfl
    obtain ⟨hm, -, -, -⟩ := hvF.xi
    have hfS := G.sub hvS (mem_subs_xi m f)
    refine (lt_xi_psi_iff (π := .Om c) (γ := γ) (f := f) (n := m) hl.symm).mpr ⟨hgt,
      (baseOf_xi_iff m f _).mpr ⟨kTerm_lt hm P.ht rfl rfl hl.symm, ?_⟩⟩
    refine inC_mono f f (.Xi m f) f _ (G.xi_self hvS) (fun u hu hu' => ?_) (fun _ _ h => h)
    have huS := G.sub hfS hu
    have := size_le_of_mem_subs hu
    exact ih u (by simp only [Tm.size]; omega) huS (G.trans huS hvS hcS hu' h)
  | Psi κ β =>
    have hκS := G.sub hvS (mem_subs_psi_p κ β)
    rcases G.tri hκS hπS with hκπ | rfl | hπκ
    · have hne : κ ≠ .Om c := fun e => Lt.ne hκπ e
      refine (lt_psi_psi_ltT (κ := κ) (β := β) hl hne (G.asymm hκS hπS hκπ)).mpr ?_
      rcases hvF.psi_shape with rfl | ⟨c', rfl, hs'⟩ | ⟨m, δ, rfl⟩
      · exact (baseOf_om_zero _).mpr (by intro e; cases e)
      · have hc'S := G.sub hκS (mem_subs_om c')
        exact baseOf_om_psiOm (G.nf _ hc'S) hs' P.ht (ne_gt_of_le (Or.inr (lt_om_iffG.mp hκπ)))
          (fun X hX hXm hXd => by
            have hXS := G.sub hc'S (mem_subs_of_mem_summands hXm)
            have := size_le_of_mem_summands c' X hXm
            exact ih X (by simp only [Tm.size]; omega) hXS hXd)
      · have hδS := G.sub hκS (mem_subs_xi m δ)
        have hb := (baseOf_xi_iff m δ _).mp (G.base_self hvS)
        refine (baseOf_xi_iff m δ _).mpr ⟨kTerm_lt (G.nf _ hκS).xi.1 P.ht rfl rfl hl.symm, ?_⟩
        refine inC_mono δ δ _ δ _ hb.2 (fun u hu hu' => ?_) (fun _ _ h => h)
        have huS := G.sub hδS hu
        have := size_le_of_mem_subs hu
        exact ih u (by simp only [Tm.size]; omega) huS (G.trans huS hvS hcS hu' h)
    · exact absurd h (G.not_lt_of_le hcS hvS (G.le_psiOm hvS))
    · have hne : κ ≠ .Om c := fun e => Lt.ne hπκ e.symm
      exact (lt_psi_psi_gtT (κ := κ) (β := β) hl hne hπκ).mpr
        (G.not_base_of_lt_tgt hvS hπS P.hT hl hπκ hvπ)

/-- 崩壊の性質のための仮定：`π = Ω_c` のとき `Ω` の不動点 `X < c` は `X < t` -/
theorem hKLt : ∀ c, π = .Om c → ∀ X, IsOF X → X ∈ S → Lt X c → Lt X (.Psi π γ) := by
  intro c hπ X hX hXS hXc
  rcases P.hT with e | ⟨c', e, hs⟩ | ⟨n, p, e⟩
  · rw [hπ] at e; cases e; exact absurd hXc (not_lt_zero X)
  · rw [hπ] at e; cases e; exact P.below hπ hs X hXS hXc
  · rw [hπ] at e; cases e

/-- 崩壊の性質 -/
theorem coll : ∀ z, z ∈ S → inC z γ (.Psi π γ) = true → Lt z π → Lt z (.Psi π γ) :=
  P.G.coll_psi P.ht P.πS P.hKLt

/-- K2：`γ` の前線（`π` について）は `t` 未満 -/
theorem k2 : ∀ w, w ∈ fr π γ → Lt w (.Psi π γ) := by
  intro w hw
  have hwS := P.G.sub P.γS (fr_spec hw).1
  have hin := fr_of_inC γ (fun v hv hnv hvt => hnv (P.tb v (P.G.sub P.γS hv) hvt)) P.ht.psi.Ca w hw
  exact P.coll w hwS hin (fr_spec hw).2

/-- CX：`π = Ω_c`（`c` は後者）なら `c < t` -/
theorem cx {c : Tm} (hπ : π = .Om c) (hs : isSucc c = true) : Lt c (.Psi π γ) := by
  have G := P.G
  have hcS := G.sub P.πS (by rw [hπ]; exact mem_subs_om c)
  have hcF := G.nf _ hcS
  cases hpc : isPrincipal c
  · cases c with
    | zero => simp [isSucc, summands] at hs
    | plus a b =>
      have haS := G.sub hcS (subs_plus_l (self_mem_subs a))
      exact (lt_plus_prin_iffY hcF rfl).mpr (P.below hπ hs a haS (lt_plus_leftY hcF))
    | _ => simp [isPrincipal] at hpc
  · -- `c = 1`
    have hc1 : c = one := by
      obtain ⟨ys, hys⟩ := summands_of_isSucc hs
      rw [summands_principal hpc] at hys
      cases ys with
      | nil => simpa using hys
      | cons _ _ => simp at hys
    subst hc1
    subst hπ
    have hl : lev (Tm.Om .zero) = lev (Tm.Om one) := rfl
    have h01 : Lt (Tm.Om .zero) (Tm.Om one) := lt_om_iffG.mpr (zero_lt (by intro e; cases e))
    have h0S : Tm.Om .zero ∈ S := G.sub hcS (mem_subs_psi_p _ _)
    exact (lt_psi_psi_ltT hl (fun e => by cases e) (G.asymm h0S P.πS h01)).mpr
      ((baseOf_om_zero _).mpr (by intro e; cases e))

end PsiCtx

end MahloOCF

namespace MahloOCF

open Tm

namespace PsiCtx

variable {S : List Tm} {π γ : Tm} (P : PsiCtx S π γ)
include P

/-- 補題 A（`π = Ξ_m(δ)`）の主要項の場合：`δ` の前線（`π` について）のどれか以下の元は `t` 未満 -/
theorem lemA_head {m : Nat} {δ : Tm} (hπ : π = .Xi m δ) {h w : Tm} (hhS : h ∈ S)
    (hhp : isPrincipal h = true) (hw : w ∈ fr π δ) (hhw : Le h w)
    (IH : ∀ u, u ∈ S → u.size < h.size → Le u w → Lt u (.Psi π γ)) : Lt h (.Psi π γ) := by
  have G := P.G
  have hπS := P.πS
  have hδS : δ ∈ S := G.sub hπS (by rw [hπ]; exact mem_subs_xi m δ)
  have hwS := G.sub hδS (fr_spec hw).1
  have hhF := G.nf _ hhS
  have htOF : IsOF (.Psi π γ) := P.tOF hπ
  have hhπ : Lt h π := G.lt_of_le_of_lt hhS hwS hπS hhw (fr_spec hw).2
  have hlh : lev h ≤ lev π := lev_le_of_lt_gen hhπ
  rcases Nat.lt_or_eq_of_le hlh with hl | hl
  · exact lt_of_lev_lt' hl
  by_cases hb : isBot h = true
  · exact bot_ltY hb (by show lev h ≤ lev π; omega) rfl rfl P.ht
  rcases shape_prin hhp (Bool.eq_false_iff.mpr hb) with ⟨x, rfl⟩ | ⟨m', f, rfl⟩ | ⟨κ, β, rfl⟩
  · have hx := G.sub hhS (mem_subs_om x)
    exact (lt_om_OFG htOF P.ht).mpr (IH x hx (by simp only [Tm.size]; omega)
      (Or.inr (G.lt_of_lt_of_le hx hhS hwS (G.lt_om_selfS x hhS) hhw)))
  · have hfS := G.sub hhS (mem_subs_xi m' f)
    have hgt : cmp π (.Xi m' f) = .gt := by unfold Lt at hhπ; rw [G.swap hhS hπS, hhπ]; rfl
    refine (lt_xi_psi_iff (π := π) (γ := γ) (f := f) (n := m') hl.symm).mpr ⟨hgt,
      (baseOf_xi_iff m' f _).mpr ⟨kTerm_lt hhF.xi.1 P.ht rfl rfl hl.symm, ?_⟩⟩
    refine inC_mono f f (.Xi m' f) f _ (G.xi_self hhS) (fun u hu hu' => ?_) (fun _ _ h => h)
    have huS := G.sub hfS hu
    have := size_le_of_mem_subs hu
    exact IH u huS (by simp only [Tm.size]; omega) (Or.inr (G.lt_of_lt_of_le huS hhS hwS hu' hhw))
  · have hκS := G.sub hhS (mem_subs_psi_p κ β)
    rcases G.tri hκS hπS with hκπ | rfl | hπκ
    · have hne : κ ≠ π := fun e => Lt.ne hκπ e
      refine (lt_psi_psi_ltT (κ := κ) (β := β) hl hne (G.asymm hκS hπS hκπ)).mpr ?_
      rcases hhF.psi_shape with rfl | ⟨c', rfl, hs'⟩ | ⟨m'', δ', rfl⟩
      · exact (baseOf_om_zero _).mpr (by intro e; cases e)
      · have hc'S := G.sub hκS (mem_subs_om c')
        refine (baseOf_om_OF (G.nf _ hc'S) hs' htOF P.ht).mpr ?_
        exact IH c' hc'S (by simp only [Tm.size]; omega) (G.le_trans hc'S hhS hwS (G.le_psiOm hhS) hhw)
      · have hδ'S := G.sub hκS (mem_subs_xi m'' δ')
        have hb' := (baseOf_xi_iff m'' δ' _).mp (G.base_self hhS)
        refine (baseOf_xi_iff m'' δ' _).mpr ⟨kTerm_lt (G.nf _ hκS).xi.1 P.ht rfl rfl hl.symm, ?_⟩
        refine inC_mono δ' δ' _ δ' _ hb'.2 (fun u hu hu' => ?_) (fun _ _ h => h)
        have huS := G.sub hδ'S hu
        have := size_le_of_mem_subs hu
        exact IH u huS (by simp only [Tm.size]; omega) (Or.inr (G.lt_of_lt_of_le huS hhS hwS hu' hhw))
    · -- `h = Ψ_π(β)`：`w < h`（`h` の K2T）に反する
      exfalso
      have hw' := hw
      exact G.not_lt_of_le hhS hwS hhw (G.k2t _ β hhS w (by rw [hπ, fr_self_xi]; rw [hπ] at hw'; exact hw'))
    · have hne : κ ≠ π := fun e => Lt.ne hπκ e.symm
      exact (lt_psi_psi_gtT (κ := κ) (β := β) hl hne hπκ).mpr
        (G.not_base_of_lt_tgt hhS hπS P.hT hl hπκ hhπ)

theorem lemA_aux {m : Nat} {δ : Tm} (hπ : π = .Xi m δ) : ∀ N, ∀ v, v ∈ S → v.size ≤ N →
    (∃ w, w ∈ fr π δ ∧ Le v w) → Lt v (.Psi π γ) := by
  have G := P.G
  have hπS := P.πS
  have hδS : δ ∈ S := G.sub hπS (by rw [hπ]; exact mem_subs_xi m δ)
  intro N
  induction N with
  | zero => intro v _ h; exact absurd h (by have := Tm.size_pos v; omega)
  | succ N ih =>
    intro v hvS hs ⟨w, hw, hvw⟩
    have hvF := G.nf _ hvS
    have hwS := G.sub hδS (fr_spec hw).1
    cases hsv : summands v with
    | nil =>
      have : v = .zero := by cases v <;> simp_all [summands]
      subst this
      exact zero_lt (by intro e; cases e)
    | cons h rest =>
      have hmem : h ∈ summands v := by rw [hsv]; exact List.mem_cons_self
      have hhS := G.sub hvS (mem_subs_of_mem_summands hmem)
      obtain ⟨-, hhp⟩ := summands_WNF v hvF h hmem
      have hhs := size_le_of_mem_summands v h hmem
      have hhw : Le h w := G.le_trans hhS hvS hwS (head_leY hvF hsv) hvw
      have hht := P.lemA_head hπ hhS hhp hw hhw (fun u hu hus huw =>
        ih u hu (by omega) ⟨w, hw, huw⟩)
      exact lt_of_head_lt rfl hsv ((lt_principal_iff hhp rfl).mp hht)

/-- K2T：崩壊先の前線（`π` について）は `t` 未満 -/
theorem k2t : ∀ w, w ∈ fr π π → Lt w (.Psi π γ) := by
  have G := P.G
  have hπS := P.πS
  intro w hw
  rcases P.hT with e | ⟨c, e, hs⟩ | ⟨m, δ, e⟩
  · subst e; simp [fr] at hw
  · have hcS : c ∈ S := G.sub hπS (by rw [e]; exact mem_subs_om c)
    have hw' : w ∈ fr π c := by rw [e, fr_self_om] at hw; rw [e]; exact hw
    have hwS := G.sub hcS (fr_spec hw').1
    rcases G.fr_le hπS hcS hw' with h' | h'
    · rw [h']; exact P.cx e hs
    · exact P.below e hs w hwS h'
  · have hδS : δ ∈ S := G.sub hπS (by rw [e]; exact mem_subs_xi m δ)
    have hw' : w ∈ fr π δ := by rw [e, fr_self_xi] at hw; rw [e]; exact hw
    exact P.lemA_aux e _ w (G.sub hδS (fr_spec hw').1) (Nat.le_refl _) ⟨w, hw', Le.refl _⟩

/-- `t` 未満の崩壊先は `t` の底の条件を満たす -/
theorem base_of_lt_t {κ β : Tm} (hq : Tm.Psi κ β ∈ S) (hl : lev κ = lev π)
    (hκt : Lt κ (.Psi π γ)) : baseOf κ (.Psi π γ) = true := by
  have G := P.G
  rcases (G.nf _ hq).psi_shape with rfl | ⟨c', rfl, hs'⟩ | ⟨m, δ', rfl⟩
  · exact (baseOf_om_zero _).mpr (by intro e; cases e)
  · have hc'S := G.sub hq (subs_psi_p (mem_subs_om c'))
    rcases P.hT with e | ⟨c, e, hs⟩ | ⟨n, p, e⟩
    · subst e; exact absurd (lt_om_psiOmG.mp hκt) (not_lt_zero c')
    · subst e
      exact baseOf_om_psiOm (G.nf _ hc'S) hs' P.ht (ne_gt_of_le (Or.inr (lt_om_psiOmG.mp hκt)))
        (fun X hX hXm hXd => P.hKLt c rfl X hX (G.sub hc'S (mem_subs_of_mem_summands hXm)) hXd)
    · exact (baseOf_om_OF (G.nf _ hc'S) hs' (P.tOF e) P.ht).mpr ((lt_om_OFG (P.tOF e) P.ht).mp hκt)
  · exact ((lt_xi_psi_iff (π := π) (γ := γ) (f := δ') (n := m) hl.symm).mp hκt).2

/-- `t = Ψ_π(γ)` は `S` を切断する -/
theorem cut : CutT S (.Psi π γ) := by
  have G := P.G
  have hπS := P.πS
  have hγS := P.γS
  refine G.cut_of_principal P.ht P.hsub (fun N ih _ q p hqS hpS hqp hpp hN h1 h2 => ?_)
  have hqF := G.nf q hqS
  have hpF := G.nf p hpS
  refine cut_reduceY P.ht rfl rfl hqF hpF hqp hpp h1 h2 (fun lq lp bq bp => ?_)
  have hpπ : Lt p π := P.tb p hpS h2
  have hqπ : Lt q π := G.trans hqS hpS hπS h1 hpπ
  -- `p` 未満の小さい元は `t` 未満
  have viaP : ∀ v, v ∈ S → v.size < q.size → Lt v p → Lt v (.Psi π γ) := fun v hvS hvs hvp =>
    ih p v hpS hvS (by omega) hvp h2
  -- `t < q` のとき、`p` の部分項 `v < t` は `v < q`
  have up : ∀ v, v ∈ S → v.size < p.size → Lt v (.Psi π γ) → Lt (.Psi π γ) q → Lt v q :=
    fun v hvS hvs hvt htq => by
      rcases G.tri hvS hqS with h' | rfl | h'
      · exact h'
      · exact absurd htq (fun h'' => P.asymm_t hvS hvt h'')
      · exact absurd htq (fun h'' => P.asymm_t hqS (ih v q hvS hqS (by omega) h' hvt) h'')
  rcases shape_prin hqp bq with ⟨y, rfl⟩ | ⟨m, f, rfl⟩ | ⟨κ', β, rfl⟩
  · -- `q = Ω_y`
    have hyS := G.sub hqS (mem_subs_om y)
    rcases P.hT with e | ⟨c, e, -⟩ | ⟨n, δ, e⟩
    · subst e; exact lt_om_psiOmG.mpr (lt_om_iffG.mp hqπ)
    · subst e; exact lt_om_psiOmG.mpr (lt_om_iffG.mp hqπ)
    · have hyp := G.trans hyS hqS hpS (G.lt_om_selfS y hqS) h1
      exact (lt_om_OFG (P.tOF e) P.ht).mpr (viaP y hyS (by simp only [Tm.size]; omega) hyp)
  · -- `q = Ξ_m(f)`
    have hfS := G.sub hqS (mem_subs_xi m f)
    have hgt : cmp π (.Xi m f) = .gt := by unfold Lt at hqπ; rw [G.swap hqS hπS, hqπ]; rfl
    refine (lt_xi_psi_iff (π := π) (γ := γ) (f := f) (n := m) lq.symm).mpr ⟨hgt,
      (baseOf_xi_iff m f _).mpr ⟨kTerm_lt hqF.xi.1 P.ht rfl rfl lq.symm, ?_⟩⟩
    refine inC_mono f f (.Xi m f) f _ (G.xi_self hqS) (fun u hu hu' => ?_) (fun _ _ h => h)
    have huS := G.sub hfS hu
    have := size_le_of_mem_subs hu
    exact viaP u huS (by simp only [Tm.size]; omega) (G.trans huS hqS hpS hu' h1)
  · -- `q = Ψ_{κ'}(β)`
    have hκ'S := G.sub hqS (mem_subs_psi_p κ' β)
    have hl : lev κ' = lev π := lq
    rcases G.tri hκ'S hπS with hκ'π | rfl | hπκ'
    · -- `κ' < π`：`q` の底の条件を `t` に移す
      have hne : κ' ≠ π := fun e => Lt.ne hκ'π e
      refine (lt_psi_psi_ltT (κ := κ') (β := β) hl hne (G.asymm hκ'S hπS hκ'π)).mpr ?_
      rcases hqF.psi_shape with rfl | ⟨c', rfl, hs'⟩ | ⟨m', δ', rfl⟩
      · exact (baseOf_om_zero _).mpr (by intro e; cases e)
      · have hc'S := G.sub hκ'S (mem_subs_om c')
        rcases P.hT with e | ⟨c, e, hs⟩ | ⟨n, p', e⟩
        · subst e; exact absurd (lt_om_iffG.mp hκ'π) (not_lt_zero c')
        · subst e
          exact baseOf_om_psiOm (G.nf _ hc'S) hs' P.ht (ne_gt_of_le (Or.inr (lt_om_iffG.mp hκ'π)))
            (fun X hX hXm hXd => P.hKLt c rfl X hX (G.sub hc'S (mem_subs_of_mem_summands hXm)) hXd)
        · have hc'q := G.lt_of_le_of_lt hc'S hqS hpS (G.le_psiOm hqS) h1
          exact (baseOf_om_OF (G.nf _ hc'S) hs' (P.tOF e) P.ht).mpr
            (viaP c' hc'S (by simp only [Tm.size]; omega) hc'q)
      · have hδ'S := G.sub hκ'S (mem_subs_xi m' δ')
        have hb' := (baseOf_xi_iff m' δ' _).mp (G.base_self hqS)
        refine (baseOf_xi_iff m' δ' _).mpr ⟨kTerm_lt (G.nf _ hκ'S).xi.1 P.ht rfl rfl hl.symm, ?_⟩
        refine inC_mono δ' δ' _ δ' _ hb'.2 (fun u hu hu' => ?_) (fun _ _ h => h)
        have huS := G.sub hδ'S hu
        have := size_le_of_mem_subs hu
        exact viaP u huS (by simp only [Tm.size]; omega) (G.trans huS hqS hpS hu' h1)
    · -- `κ' = π`：`β < γ` を `p` の形で示す
      rcases P.lt_or_gt hqS with hqt | htq
      · exact hqt
      exfalso
      rcases shape_prin hpp bp with ⟨x, rfl⟩ | ⟨m', f, rfl⟩ | ⟨κ, α, rfl⟩
      · -- `p = Ω_x`
        have hxS := G.sub hpS (mem_subs_om x)
        rcases P.hT with e | ⟨c, e, -⟩ | ⟨n, δ, e⟩
        · subst e; exact not_lt_zero x (lt_om_psiOmG.mp h2)
        · subst e
          have hcS := G.sub hπS (mem_subs_om c)
          exact G.not_lt_of_le hcS hxS ((G.lt_psiOm_omS hqS hxS).mp h1) (lt_om_psiOmG.mp h2)
        · have hX : IsOF (.Psi κ' β) := by subst e; exact Or.inr ⟨n, δ, β, rfl⟩
          have hqx := (G.lt_OF_omS hX hqS hxS).mp h1
          have hxt := (lt_om_OFG (P.tOF e) P.ht).mp h2
          exact P.asymm_t hqS (ih x _ hxS hqS (by simp only [Tm.size] at hN ⊢; omega) hqx hxt) htq
      · -- `p = Ξ_m'(f)`：`f ∈ C(f, t) ⊆ C(f, q)`
        have hfS := G.sub hpS (mem_subs_xi m' f)
        have hft := ((baseOf_xi_iff m' f _).mp ((lt_xi_psi_iff (π := κ') (γ := γ) (f := f) (n := m')
          lp.symm).mp h2).2).2
        have hfq : inC f f (.Psi κ' β) = true := inC_mono f f _ f _ hft (fun u hu hut => by
          have := size_le_of_mem_subs hu
          exact up u (G.sub hfS hu) (by simp only [Tm.size]; omega) hut htq) (fun _ _ h => h)
        rcases (lt_psi_xiY (π := κ') (a := β) (b := f) (n := m') lp.symm).mp h1 with h' | h'
        · exact G.not_lt_of_le hκ'S hpS (G.le_of_ne_gt hκ'S hpS h') hpπ
        · rw [baseOf_xi, hfq, Bool.and_true] at h'
          have := kTerm_lt (n := m') hpF.xi.1 hqF rfl rfl lp.symm
          unfold Lt at this; rw [this] at h'; cases h'
      · -- `p = Ψ_κ(α)`
        have hκS := G.sub hpS (mem_subs_psi_p κ α)
        have hlκ : lev κ = lev κ' := lp
        rcases G.tri hκS hκ'S with hκπ | rfl | hπκ
        · -- `κ < π`：`Base_κ(t)` から `Base_κ(q)`
          have hne : κ ≠ κ' := fun e => Lt.ne hκπ e
          have hbt := (lt_psi_psi_ltT (κ := κ) (β := α) hlκ hne (G.asymm hκS hκ'S hκπ)).mp h2
          have hbq := (lt_psi_psi_gtT (κ := κ') (β := β) (π := κ) (γ := α) hlκ.symm
            (fun e => hne e.symm) hκπ).mp h1
          rcases hpF.psi_shape with rfl | ⟨c', rfl, hs'⟩ | ⟨m'', δ', rfl⟩
          · rw [(baseOf_om_zero _).mpr (by intro e; cases e)] at hbq; cases hbq
          · have hc'S := G.sub hκS (mem_subs_om c')
            rcases P.hT with e | ⟨c, e, hs⟩ | ⟨n, δ, e⟩
            · subst e; exact not_lt_zero c' (lt_om_iffG.mp hκπ)
            · subst e
              rw [baseOf_om_psiOm (G.nf _ hc'S) hs' hqF (ne_gt_of_le (Or.inr (lt_om_iffG.mp hκπ)))
                (fun X hX hXm hXd => (G.lt_OF_psiOmS hX (G.sub hc'S (mem_subs_of_mem_summands hXm))
                  hqS).mpr hXd)] at hbq
              cases hbq
            · have hX : IsOF (.Psi κ' β) := by subst e; exact Or.inr ⟨n, δ, β, rfl⟩
              have hc't := (baseOf_om_OF (G.nf _ hc'S) hs' (P.tOF e) P.ht).mp hbt
              have hc'q := up c' hc'S (by simp only [Tm.size]; omega) hc't htq
              rw [(baseOf_om_OF (G.nf _ hc'S) hs' hX hqF).mpr hc'q] at hbq
              cases hbq
          · have hδ'S := G.sub hκS (mem_subs_xi m'' δ')
            have hδt := ((baseOf_xi_iff m'' δ' _).mp hbt).2
            have hδq : inC δ' δ' (.Psi κ' β) = true := inC_mono δ' δ' _ δ' _ hδt (fun u hu hut => by
              have := size_le_of_mem_subs hu
              exact up u (G.sub hδ'S hu) (by simp only [Tm.size]; omega) hut htq) (fun _ _ h => h)
            rw [(baseOf_xi_iff m'' δ' _).mpr ⟨kTerm_lt (G.nf _ hκS).xi.1 hqF rfl rfl hlκ.symm, hδq⟩]
              at hbq
            cases hbq
        · -- `κ = π`：`β < α < γ`
          exact P.asymm_t hqS (lt_psi_psi_same.mpr (G.trans (G.sub hqS (mem_subs_psi_a _ β))
            (G.sub hpS (mem_subs_psi_a _ α)) hγS (lt_psi_psi_same.mp h1) (lt_psi_psi_same.mp h2))) htq
        · -- `κ > π`：`Base_π(p)` と `¬ Base_π(p)`
          have hne : κ ≠ κ' := fun e => Lt.ne hπκ e.symm
          have hb1 := (lt_psi_psi_ltT (κ := κ') (β := β) (π := κ) (γ := α) hlκ.symm
            (fun e => hne e.symm) (G.asymm hκ'S hκS hπκ)).mp h1
          have hb2 := (lt_psi_psi_gtT (κ := κ) (β := α) hlκ hne hπκ).mp h2
          rw [hb1] at hb2; cases hb2
    · -- `κ' > π`
      have hne : κ' ≠ π := fun e => Lt.ne hπκ' e.symm
      exact (lt_psi_psi_gtT (κ := κ') (β := β) hl hne hπκ').mpr
        (G.not_base_of_lt_tgt hqS hπS P.hT hl hπκ' hqπ)

end PsiCtx

end MahloOCF

/-! ## 有限集合の上の不変条件と、体系全体の順序の性質 -/

namespace MahloOCF

open Tm

theorem lin_closedY : ∀ n, ∀ S : List Tm, S.length ≤ n →
    (∀ s, s ∈ S → ∀ r, r ∈ subs s → r ∈ S) → (∀ s, s ∈ S → WNF s) → GoodY S := by
  intro n
  induction n with
  | zero =>
    intro S hl _ _
    have hS : S = [] := List.eq_nil_of_length_eq_zero (Nat.le_zero.mp hl)
    subst hS
    exact GoodY.nil
  | succ n ih =>
    intro S hl hcl hNF
    by_cases hS0 : S = []
    · subst hS0
      exact GoodY.nil
    obtain ⟨t, htS, hmax⟩ := exists_max_size S hS0
    have hmem : ∀ s, s ∈ S.filter (fun s => s != t) ↔ s ∈ S ∧ s ≠ t := by
      intro s
      rw [List.mem_filter, bne_iff_ne]
    have hl' : (S.filter (fun s => s != t)).length ≤ n := by
      have := length_filter_ne_lt htS
      omega
    have hcl' : ∀ s, s ∈ S.filter (fun s => s != t) → ∀ r, r ∈ subs s →
        r ∈ S.filter (fun s => s != t) := by
      intro s hs r hr
      obtain ⟨hsS, hst⟩ := (hmem s).mp hs
      refine (hmem r).mpr ⟨hcl s hsS r hr, ?_⟩
      intro e
      subst e
      exact hst (eq_of_mem_subs_size hr (hmax s hsS)).symm
    have hNF' : ∀ s, s ∈ S.filter (fun s => s != t) → WNF s := fun s hs =>
      hNF s ((hmem s).mp hs).1
    have G' := ih _ hl' hcl' hNF'
    have htF := hNF t htS
    have hsub : ∀ s, s ∈ subs t → s ≠ t → s ∈ S.filter (fun s => s != t) := fun s hs hne =>
      (hmem s).mpr ⟨hcl t htS s hs, hne⟩
    have htS' : t ∉ S.filter (fun s => s != t) := fun h => ((hmem t).mp h).2 rfl
    have inS' : ∀ s, s ∈ S → s ≠ t → s ∈ S.filter (fun s => s != t) := fun s hs hne =>
      (hmem s).mpr ⟨hs, hne⟩
    have cut : CutT (S.filter (fun s => s != t)) t := by
      cases t with
      | zero => exact cut_botY G' htF (Or.inr rfl) hsub
      | M _ => exact cut_botY G' htF (Or.inl rfl) hsub
      | plus a b =>
        exact G'.cut_of_principal htF hsub (fun _ _ htp => by simp [isPrincipal] at htp)
      | Om e => exact cut_omY G' htF hsub
      | Xi m γ => exact (XiCtx.mk G' htF hsub htS').cut
      | Psi π γ => exact (PsiCtx.mk G' htF hsub htS').cut
    have hA := antiOn_extend G'.anti inS' (G'.anti_new htF hsub htS')
    refine ⟨linOn_of_cutY hA G'.lin inS' cut, hA, hNF, hcl, ?_, ?_, ?_, ?_⟩
    · intro π γ hx
      by_cases e : Tm.Psi π γ = t
      · subst e
        exact (PsiCtx.mk G' htF hsub htS').k2
      · exact G'.k2 π γ (inS' _ hx e)
    · intro π γ hx
      by_cases e : Tm.Psi π γ = t
      · subst e
        exact (PsiCtx.mk G' htF hsub htS').k2t
      · exact G'.k2t π γ (inS' _ hx e)
    · intro m γ hx
      by_cases e : Tm.Xi m γ = t
      · subst e
        exact (XiCtx.mk G' htF hsub htS').k2x
      · exact G'.k2x m γ (inS' _ hx e)
    · intro c γ hx hs
      by_cases e : Tm.Psi (.Om c) γ = t
      · subst e
        exact (PsiCtx.mk G' htF hsub htS').cx rfl hs
      · exact G'.cx c γ (inS' _ hx e) hs

/-- 部分項で閉じた有限集合の不変条件 -/
theorem goodY_of {S : List Tm} (hcl : ∀ s, s ∈ S → ∀ r, r ∈ subs s → r ∈ S)
    (hNF : ∀ s, s ∈ S → WNF s) : GoodY S :=
  lin_closedY _ S (Nat.le_refl _) hcl hNF

/-- 項の一覧の部分項の一覧 -/
def subsL : List Tm → List Tm
  | [] => []
  | t :: ts => subs t ++ subsL ts

theorem mem_subsL {l : List Tm} {s : Tm} : s ∈ subsL l ↔ ∃ t, t ∈ l ∧ s ∈ subs t := by
  induction l with
  | nil => simp [subsL]
  | cons t ts ih =>
    simp only [subsL, List.mem_append, ih, List.mem_cons]
    constructor
    · rintro (h | ⟨u, hu, h⟩)
      · exact ⟨t, Or.inl rfl, h⟩
      · exact ⟨u, Or.inr hu, h⟩
    · rintro ⟨u, hu | hu, h⟩
      · subst hu; exact Or.inl h
      · exact Or.inr ⟨u, hu, h⟩

/-- 標準形の一覧から作る不変条件 -/
theorem goodYL {l : List Tm} (hl : ∀ t, t ∈ l → WNF t) : GoodY (subsL l) := by
  refine goodY_of (fun s hs r hr => ?_) (fun s hs => ?_)
  · obtain ⟨t, ht, hs⟩ := mem_subsL.mp hs
    exact mem_subsL.mpr ⟨t, ht, subs_trans hs hr⟩
  · obtain ⟨t, ht, hs⟩ := mem_subsL.mp hs
    exact (hl t ht).of_mem_subs hs

theorem mem_subsL_self {l : List Tm} {t : Tm} (h : t ∈ l) : t ∈ subsL l :=
  mem_subsL.mpr ⟨t, h, self_mem_subs t⟩

/-! ### 体系全体の順序の性質 -/

theorem wnf_list2 {a b : Tm} (ha : WNF a) (hb : WNF b) : ∀ t, t ∈ [a, b] → WNF t := by
  intro t ht
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl <;> assumption

theorem wnf_list3 {a b c : Tm} (ha : WNF a) (hb : WNF b) (hc : WNF c) :
    ∀ t, t ∈ [a, b, c] → WNF t := by
  intro t ht
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
  rcases ht with rfl | rfl | rfl <;> assumption

theorem wnf_list1 {a : Tm} (ha : WNF a) : ∀ t, t ∈ [a] → WNF t := by
  intro t ht
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
  subst ht; exact ha

theorem swapY {a b : Tm} (ha : WNF a) (hb : WNF b) : cmp b a = (cmp a b).swap :=
  (goodYL (wnf_list2 ha hb)).swap (mem_subsL_self (by simp)) (mem_subsL_self (by simp))

theorem eqY {a b : Tm} (ha : WNF a) (hb : WNF b) (h : cmp a b = .eq) : a = b :=
  (goodYL (wnf_list2 ha hb)).eq (mem_subsL_self (by simp)) (mem_subsL_self (by simp)) h

theorem transY {a b c : Tm} (ha : WNF a) (hb : WNF b) (hc : WNF c) (h1 : Lt a b) (h2 : Lt b c) :
    Lt a c :=
  (goodYL (wnf_list3 ha hb hc)).trans (mem_subsL_self (by simp)) (mem_subsL_self (by simp))
    (mem_subsL_self (by simp)) h1 h2

theorem k2Y {π γ : Tm} (h : WNF (.Psi π γ)) : ∀ w, w ∈ fr π γ → Lt w (.Psi π γ) :=
  (goodYL (wnf_list1 h)).k2 π γ (mem_subsL_self (by simp))

theorem k2tY {π γ : Tm} (h : WNF (.Psi π γ)) : ∀ w, w ∈ fr π π → Lt w (.Psi π γ) :=
  (goodYL (wnf_list1 h)).k2t π γ (mem_subsL_self (by simp))

theorem k2xY {n : Nat} {γ : Tm} (h : WNF (.Xi n γ)) : ∀ w, w ∈ fr (.M n) γ → Lt w (.Xi n γ) :=
  (goodYL (wnf_list1 h)).k2x n γ (mem_subsL_self (by simp))

theorem cxY {c γ : Tm} (h : WNF (.Psi (.Om c) γ)) (hs : isSucc c = true) :
    Lt c (.Psi (.Om c) γ) :=
  (goodYL (wnf_list1 h)).cx c γ (mem_subsL_self (by simp)) hs

/-- 標準形の上で `<` は狭義全順序 -/
theorem triY {a b : Tm} (ha : WNF a) (hb : WNF b) : Lt a b ∨ a = b ∨ Lt b a := by
  cases e : cmp a b with
  | lt => exact Or.inl e
  | eq => exact Or.inr (Or.inl (eqY ha hb e))
  | gt =>
    refine Or.inr (Or.inr ?_)
    unfold Lt
    rw [swapY ha hb, e]
    rfl

theorem Lt.asymmY {a b : Tm} (ha : WNF a) (hb : WNF b) (h : Lt a b) : ¬ Lt b a := by
  unfold Lt at *
  rw [swapY ha hb, h]
  decide

end MahloOCF
