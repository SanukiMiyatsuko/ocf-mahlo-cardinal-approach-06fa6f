import Mahlo.FS.BachVK

/-! 構造的な前線の評価。`M_m⁺` 未満の項（`M_m` 以上の節点は `M_m` と `Ψ_{M_m⁺}(·)` だけ）の基本列は、
最後の加数を下っていき、最後に `M_m` 未満の節点（前線 `d`）の基本列で置き換える。したがって前線が全て
`d` 以下で、0 番目の前線が `d` 未満なら、全ての項の前線は `d` 未満。 -/

namespace MahloOCF.FS

open Tm

/-! ### 前線の補題 -/

/-- 加数の前線は和の前線 -/
theorem fr_of_mem_summands {R x u f : Tm} (hu : u ∈ summands x) (hf : f ∈ fr R u) : f ∈ fr R x :=
  mem_fr_iff.mpr ⟨u, hu, hf⟩

/-- 後ろの加数は和の加数 -/
theorem mem_summands_oadd_right {a y u : Tm} (ha : WNF a) (hy : WNF y) (hu : u ∈ summands y) :
    u ∈ summands (oadd a y) := by
  cases hs : summands y with
  | nil => rw [hs] at hu; cases hu
  | cons h r =>
    rw [summands_oadd hs (nfl_principal (nfl_summands ha)) (nfl_principal (nfl_summands hy))]
    exact List.mem_append_right _ hu

/-- 後ろの部分の前線は和の前線 -/
theorem fr_oadd_right {R a y f : Tm} (ha : WNF a) (hy : WNF y) (hf : f ∈ fr R y) :
    f ∈ fr R (oadd a y) := by
  obtain ⟨u, hu, hfu⟩ := mem_fr_iff.mp hf
  exact mem_fr_iff.mpr ⟨u, mem_summands_oadd_right ha hy hu, hfu⟩

/-- `Ψ_{M_m⁺}(a)` の前線は `a` の前線を含む -/
theorem fr_psiS_rev {m : Nat} (hm : 1 ≤ m) {a f : Tm} (h : WNF (.Psi (succM m) a))
    (hf : f ∈ fr (.M m) a) : f ∈ fr (.M m) (.Psi (succM m) a) := by
  have hlt : ¬ Lt (.Psi (succM m) a) (.M m) := Lt.asymmY (WNF.M' hm) h (M_lt_psiS hm h)
  simp only [fr, hlt, ↓reduceIte, List.mem_append]
  exact Or.inr hf

/-- `Ω_{x+1}` の前線は `x` の前線と `1` -/
theorem fr_om_sc {m : Nat} (hm : 1 ≤ m) {x f : Tm} (hf : f ∈ fr (.M m) (.Om (sc x))) :
    f ∈ fr (.M m) x ∨ f = one := by
  have hf' : f ∈ fr (.M m) (succT x) := by simpa only [fr, sc] using hf
  obtain ⟨u, hu, hfu⟩ := mem_fr_iff.mp hf'
  rw [summands_succT] at hu
  rcases List.mem_append.mp hu with hu | hu
  · exact Or.inl (mem_fr_iff.mpr ⟨u, hu, hfu⟩)
  · rw [List.mem_singleton.mp hu] at hfu; exact Or.inr (fr_M_one hm f hfu)

theorem fr_om_sc_rev {m : Nat} {x f : Tm} (hf : f ∈ fr (.M m) x) : f ∈ fr (.M m) (.Om (sc x)) := by
  obtain ⟨u, hu, hfu⟩ := mem_fr_iff.mp hf
  have h : f ∈ fr (.M m) (succT x) :=
    mem_fr_iff.mpr ⟨u, by rw [summands_succT]; exact List.mem_append_left _ hu, hfu⟩
  simpa only [fr, sc] using h

theorem omegaFixed_of_IsOF {d : Tm} (h : IsOF d) : omegaFixed d = true := by
  rcases h with ⟨n, a, rfl⟩ | ⟨n, p, β, rfl⟩ <;> rfl

/-! ### `Ψ_{M_m⁺}` の近似 -/

theorem app_psi00_nat {τ π R : Tm} {pre : List Tm} {r : SeqD} (hr : r.dom = .omega) {n : Nat}
    (hx : WNF (r.nat n)) :
    (SeqD.app τ (.psi π) pre R r .zero .zero).nat n = .Psi π (oadd (ofSummands pre) (r.nat n)) := by
  simp only [SeqD.nat, hr, Gen.ap]
  rw [combine_psi_zero pre WNF.zero hx, zero_oadd hx]

theorem app_psi00_dom_nat {τ π R : Tm} {pre : List Tm} {r : SeqD} (hr : r.dom = .omega) :
    (SeqD.app τ (.psi π) pre R r .zero .zero).dom = .omega := by
  simp only [SeqD.dom, hr]

theorem app_psi00_big_dom {τ π R σ : Tm} {pre : List Tm} {r : SeqD} (hr : r.dom = .big σ)
    (hστ : Lt σ τ) : (SeqD.app τ (.psi π) pre R r .zero .zero).dom = .big σ := by
  simp only [SeqD.dom, hr, ltB_iff.mpr hστ, ↓reduceIte]

theorem app_psi00_big {τ π R : Tm} {pre : List Tm} {r : SeqD} {ξ : Tm} (hx : WNF (r.big ξ)) :
    (SeqD.app τ (.psi π) pre R r .zero .zero).big ξ = .Psi π (oadd (ofSummands pre) (r.big ξ)) := by
  simp only [SeqD.big, Gen.ap]
  rw [combine_psi_zero pre WNF.zero hx, zero_oadd hx]

/-- `Ψ_{M_m⁺}(Y)`（`Y` は極限で `M_m⁺` 未満）の列の記述は最後の加数の近似 -/
theorem cs_succM_lim {m : Nat} {Y R : Tm} {pre : List Tm} (hY : WNF Y) (hsY : summands Y = pre ++ [R])
    (hns : ¬ isSucc Y = true) (hYS : Lt Y (succM m)) (hm : 1 ≤ m) :
    cs (succM m) Y = .app (succM m) (.psi (succM m)) pre R (info R).seq .zero .zero := by
  have hN : NFL (pre ++ [R]) := by rw [← hsY]; exact nfl_summands hY
  have hRF := (hN.1 R (by simp)).1
  have hRY : Le R Y := le_of_mem_summands hY (by rw [hsY]; simp)
  refine cs_lim_app hY hsY hns ?_ ?_
  · simp [mkApp, Gen.tgt?, argR?, tailRaw, succM]
  · intro σ hσ
    left
    have hB := (inv_of R hRF).2 σ hσ
    exact ltB_iff.mpr (lt_of_le_of_ltY hB.props.σF hRF (WNF.succM hm) hB.σle
      (lt_of_le_of_ltY hRF hY (WNF.succM hm) hRY hYS))

/-! ### 構造的な前線の評価 -/

/-- 前線 `d` についての結論：(ab) 0 番目の前線が `d` 未満なら全ての項の前線が `d` 未満（共終数は `d` 以下）、
(c) `d` の真の部分項で `d` 未満のものは、0 番目の前線の上界 `Ξ_m(A)` 未満、
(dd) `M_m` 未満で `d` と異なる項では (ab) の仮定は成り立たない（`d` が `Ω` で閉じていれば） -/
structure FrConc (m : Nat) (d T : Tm) : Prop where
  ab : (∀ f, f ∈ fr (.M m) (fund T .zero) → Lt f d) →
    (dom T = .omega → ∀ n f, f ∈ fr (.M m) (fundNat T n) → Lt f d) ∧
    (∀ σ, dom T = .big σ → Le σ d ∧
      ∀ ξ, WNF ξ → Lt ξ σ → ∀ f, f ∈ fr (.M m) (fundBig T ξ) → Lt f d)
  c : ∀ A, WNF (.Xi m A) → (∀ f, f ∈ fr (.M m) (fund T .zero) → Lt f (.Xi m A)) →
    ∀ v, v ∈ subs d → v ≠ d → Lt v d → Lt v (.Xi m A)
  dd : Lt T (.M m) → T ≠ d → IsOF d → lev d = m → Lt (floorLev m) d →
    (∀ f, f ∈ fr (.M m) (fund T .zero) → Lt f d) → False

/-- `d` 自身（`M_m` 未満の節点） -/
theorem frConc_self {m : Nat} (hm : 1 ≤ m) {d : Tm} (hdF : WNF d) (hdM : Lt d (.M m)) (hd1 : Lt one d)
    (hdn : (∃ n a, d = .Xi n a) ∨ (∃ k a, d = .Psi k a)) : FrConc m d d := by
  have hMF := WNF.M' hm
  have hdp : isPrincipal d = true := by rcases hdn with ⟨n, a, rfl⟩ | ⟨k, a, rfl⟩ <;> rfl
  have hd0 : d ≠ .zero := by intro e; rw [e] at hdp; cases hdp
  have hds : ¬ isSucc d = true := by
    rw [isSucc_principal hdp]
    intro h
    have e := beq_iff_eq.mp h
    rw [e] at hd1
    exact Lt.irrefl _ hd1
  have hI := inv_of d hdF
  refine ⟨fun _ => ⟨fun hd n f hf => ?_, fun σ hd => ?_⟩, fun A hA h v hv hne hvd => ?_,
    fun _ hne => absurd rfl hne⟩
  · have hN := hI.1 hd
    have hxF := hN.props.nf n
    have hxd := hN.props.lt n
    exact lt_of_le_of_ltY (fr_elem hxF hf).1 hxF hdF
      (fr_le_of_lt hMF _ hxF (lt_transY hxF hdF hMF hxd hdM) f hf) hxd
  · have hB := hI.2 σ hd
    refine ⟨hB.σle, fun ξ hξ hξσ f hf => ?_⟩
    have hxF := hB.props.nf ξ hξ hξσ
    have hxd := hB.props.lt ξ hξ hξσ
    exact lt_of_le_of_ltY (fr_elem hxF hf).1 hxF hdF
      (fr_le_of_lt hMF _ hxF (lt_transY hxF hdF hMF hxd hdM) f hf) hxd
  · have hvF := hdF.of_mem_subs hv
    have h0F := wnf_f0 hdF
    have h0d := f0_lt hdF hd0
    have hv0 : Lt v (fund d .zero) := by
      cases e : dom d with
      | zero => exact absurd ((dom_eq_zero_iff hdF).mp e) hd0
      | one => exact absurd ((dom_eq_one_iff hdF).mp e) hds
      | omega => rw [fund_zero_omega e]; exact (hI.1 e).gap 0 v hv hne hvd
      | big σ =>
        have hB := hI.2 σ e
        rw [fund_zero_big e]
        exact hB.gapP hdp .zero v WNF.zero hB.props.pos hv hne hvd
    have h0y : Lt (fund d .zero) (.Xi m A) :=
      below_of_frM hm hA (Or.inl ⟨m, A, rfl⟩) rfl (floorLev_lt_xi hA) _ h0F
        (lt_transY h0F hdF hMF h0d hdM) h
    exact lt_transY hvF h0F hA hv0 h0y

/-- 構造的な前線の評価：`M_m⁺` 未満で `M_m` 以上の節点の引数が `M_m⁺` 未満の項 `T` の前線 `d`（前線は全て
`d` 以下）について -/
theorem fr_fs_low {m : Nat} (hm : 1 ≤ m) {d : Tm} (hdF : WNF d) (hd1 : Lt one d) :
    ∀ T : Tm, WNF T → Lt T (succM m) → inC T (succM m) (.M m) = true →
      d ∈ fr (.M m) T → (∀ f, f ∈ fr (.M m) T → Le f d) → FrConc m d T := by
  have hMF := WNF.M' hm
  have hSF := WNF.succM hm
  have hd1' : d ≠ one := fun e => by rw [e] at hd1; exact Lt.irrefl _ hd1
  -- `d` が 0 番目の前線なら空
  have vac : ∀ T, d ∈ fr (.M m) (fund T .zero) → FrConc m d T := fun T hd0 =>
    ⟨fun h => (Lt.irrefl _ (h d hd0)).elim,
      fun A hA h v hv _ hvd => lt_transY (hdF.of_mem_subs hv) hdF hA hvd (h d hd0),
      fun _ _ _ _ _ h => Lt.irrefl _ (h d hd0)⟩
  intro T
  induction T using size_induction with
  | h T ih =>
  intro hT hTS hTC hdT hfrT
  by_cases hsT : isSucc T = true
  · -- 後者：0 番目は `T - 1` で、`d` はその前線
    apply vac
    have hf0 : fund T .zero = predT T := by
      rw [fund_eq, (dom_eq_one_iff hT).mpr hsT]; rfl
    rw [hf0]
    obtain ⟨ys, hys⟩ := summands_of_isSucc hsT
    obtain ⟨u, hu, hdu⟩ := mem_fr_iff.mp hdT
    rw [hys] at hu
    rcases List.mem_append.mp hu with hu | hu
    · exact mem_fr_iff.mpr ⟨u, by rw [summands_predT hT hys]; exact hu, hdu⟩
    · rw [List.mem_singleton.mp hu] at hdu
      exact absurd (fr_M_one hm d hdu) hd1'
  cases T with
  | zero => simp [fr] at hdT
  | M n => simp [fr] at hdT
  | plus a b =>
    obtain ⟨haF, hbF, hap, hb0⟩ := hT.plus
    have hbs : ¬ isSucc b = true := fun h =>
      hsT ((dom_eq_one_iff hT).mp (by rw [dom_plus]; exact (dom_eq_one_iff hbF).mpr h))
    have hdb : dom b ≠ .one := fun e => hbs ((dom_eq_one_iff hbF).mp e)
    have hf0 : fund (.plus a b) .zero = oadd a (fund b .zero) := f0_plus hT hdb
    have hb0F := wnf_f0 hbF
    have haT0 : a ∈ summands (fund (.plus a b) .zero) := by
      rw [hf0]
      cases hx : summands (fund b .zero) with
      | nil => rw [eq_zero_of_summands_nil hx, oadd_zero, summands_principal hap]; simp
      | cons h r =>
        rw [summands_oadd hx (nfl_principal (nfl_summands haF)) (nfl_principal (nfl_summands hb0F)),
          summands_principal hap]
        obtain ⟨h', r', hb'⟩ := List.exists_cons_of_ne_nil (summands_ne_nil hb0)
        have e1 := head_le_of_lt hx hb' (f0_lt hbF hb0)
        have hhW := summands_WNF _ hb0F h (by rw [hx]; exact List.mem_cons_self)
        have hh'W := summands_WNF _ hbF h' (by rw [hb']; exact List.mem_cons_self)
        have hha : Le h a := le_transY hhW.1 hh'W.1 haF
          (le_of_ne_gtY hhW.1 hh'W.1 (by rw [cmp_principal hhW.2 hh'W.2]; exact e1))
          (le_of_ne_gtY hh'W.1 haF (WNF.plus_head hT hb'))
        simp [le_leB hha]
    have hfrA : ∀ f, f ∈ fr (.M m) a → f ∈ fr (.M m) (fund (.plus a b) .zero) := fun f hf =>
      fr_of_mem_summands haT0 hf
    have hfrB0 : ∀ f, f ∈ fr (.M m) (fund b .zero) → f ∈ fr (.M m) (fund (.plus a b) .zero) :=
      fun f hf => by rw [hf0]; exact fr_oadd_right haF hb0F hf
    have hdT' : d ∈ fr (.M m) a ∨ d ∈ fr (.M m) b := by
      simpa only [fr, List.mem_append] using hdT
    rcases hdT' with hda | hdb'
    · exact vac _ (hfrA d hda)
    have hbS : Lt b (succM m) := lt_transY hbF hT hSF (lt_plus_rightY hT) hTS
    have hbC : inC b (succM m) (.M m) = true := by
      rw [inC_plus, Bool.and_eq_true] at hTC; exact hTC.2
    have hfrb : ∀ f, f ∈ fr (.M m) b → Le f d := fun f hf =>
      hfrT f (by simp only [fr, List.mem_append]; exact Or.inr hf)
    have IH := ih b (by simp only [Tm.size]; omega) hbF hbS hbC hdb' hfrb
    refine ⟨fun h0 => ?_, fun A hA h0 => IH.c A hA (fun f hf => h0 f (hfrB0 f hf)),
      fun hTM _ hOF hl hbot h0 => ?_⟩
    · have hab := IH.ab (fun f hf => h0 f (hfrB0 f hf))
      have hfa : ∀ f, f ∈ fr (.M m) a → Lt f d := fun f hf => h0 f (hfrA f hf)
      refine ⟨fun hd n f hf => ?_, fun σ hd => ⟨(hab.2 σ hd).1, fun ξ hξ hξσ f hf => ?_⟩⟩
      · have hd' : dom b = .omega := hd
        rw [fundNat_plus] at hf
        rcases fr_oadd_cases haF (((props_all b hbF).1 hd').nf n) hf with hf | hf
        · exact hfa f hf
        · exact hab.1 hd' n f hf
      · have hd' : dom b = .big σ := hd
        rw [fundBig_plus] at hf
        rcases fr_oadd_cases haF (((props_all b hbF).2 σ hd').nf ξ hξ hξσ) hf with hf | hf
        · exact hfa f hf
        · exact (hab.2 σ hd').2 ξ hξ hξσ f hf
    · by_cases hbd : b = d
      · -- `a ≥ d`：`a` の前線に `d` 以上のものがある
        have hda : Le d a := by
          have hs : summands b = [d] := by rw [hbd]; exact summands_principal (IsOF.principal hOF)
          exact le_of_ne_gtY hdF haF (WNF.plus_head hT hs)
        have haM : Lt a (.M m) := lt_transY haF hT hMF (lt_plus_leftY hT) hTM
        have hlt := below_of_frM hm hdF hOF hl hbot a haF haM (fun w hw => h0 w (hfrA w hw))
        exact not_lt_of_leY hdF haF hda hlt
      · have hbM : Lt b (.M m) := lt_transY hbF hT hMF (lt_plus_rightY hT) hTM
        exact IH.dd hbM hbd hOF hl hbot (fun f hf => h0 f (hfrB0 f hf))
  | Om e =>
    obtain ⟨heF, heOF⟩ := hT.om
    have hde : d ∈ fr (.M m) e := by simpa only [fr] using hdT
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
    by_cases hreg : omReg e
    · rcases hreg with he0 | hes
      · subst he0; simp [fr] at hde
      · -- `T[0] = Ψ_{Ω_e}(0)` は `d` より大きい
        have hdom := dom_om_reg (Or.inr hes)
        have hB := (inv_of _ hT).2 _ hdom
        have hf0 : fund (.Om e) .zero = .Psi (.Om e) .zero := f0_om_reg (Or.inr hes)
        have hP0F : WNF (.Psi (.Om e) .zero) := by rw [← hf0]; exact wnf_f0 hT
        have hP0M : Lt (.Psi (.Om e) .zero) (.M m) :=
          lt_transY hP0F hT hMF (lt_psi_targetY hP0F) hTM
        have hPfr : Tm.Psi (.Om e) .zero ∈ fr (.M m) (fund (.Om e) .zero) := by
          rw [hf0]; exact mem_fr_self (Or.inr ⟨_, _, rfl⟩) hP0M
        have hdsub : d ∈ subs (.Om e) := (fr_spec hdT).1
        have hdne : d ≠ .Om e := by
          intro h
          rcases fr_node hdT with ⟨n, a, h'⟩ | ⟨k, a, h'⟩ <;> rw [h'] at h <;> cases h
        have hdlt : Lt d (.Om e) := lt_of_le_of_ltY hdF heF hT (fr_leY hMF heF hde) (lt_om_selfY hT)
        have hdP : Lt d (.Psi (.Om e) .zero) := by
          have h := hB.gapP rfl .zero d WNF.zero hB.props.pos hdsub hdne hdlt
          rw [fundBig_om_reg (Or.inr hes), oadd_zero] at h
          exact h
        refine ⟨fun h0 => (Lt.asymmY hdF hP0F hdP (h0 _ hPfr)).elim,
          fun A hA h0 v hv _ hvd => ?_, fun _ _ _ _ _ h0 => Lt.asymmY hdF hP0F hdP (h0 _ hPfr)⟩
        exact lt_transY (hdF.of_mem_subs hv) hdF hA hvd (lt_transY hdF hP0F hA hdP (h0 _ hPfr))
    · -- `e` は極限：`T[n] = Ω_{e[n]+1}`
      have hdom : dom (.Om e) = dom e := dom_om_lim hreg
      have hf0 : fund (.Om e) .zero = .Om (sc (fund e .zero)) := f0_om_lim hT hreg
      have heS' : Lt e (succM m) := lt_transY heF hT hSF (lt_om_selfY hT) hTS
      have heC : inC e (succM m) (.M m) = true := by rw [inC_om] at hTC; exact hTC
      have hfre : ∀ f, f ∈ fr (.M m) e → Le f d := fun f hf =>
        hfrT f (by simpa only [fr] using hf)
      have IH := ih e (by simp only [Tm.size]; omega) heF heS' heC hde hfre
      have h0e : ∀ f, f ∈ fr (.M m) (fund e .zero) → f ∈ fr (.M m) (fund (.Om e) .zero) :=
        fun f hf => by rw [hf0]; exact fr_om_sc_rev hf
      refine ⟨fun h0 => ?_, fun A hA h0 => IH.c A hA (fun f hf => h0 f (h0e f hf)),
        fun _ _ hOF hl hbot h0 => ?_⟩
      · have hab := IH.ab (fun f hf => h0 f (h0e f hf))
        refine ⟨fun hd n f hf => ?_, fun σ hd => ?_⟩
        · have hd' : dom e = .omega := by rw [← hdom]; exact hd
          rw [fundNat_om hreg] at hf
          rcases fr_om_sc hm hf with hf | hf
          · exact hab.1 hd' n f hf
          · rw [hf]; exact hd1
        · have hd' : dom e = .big σ := by rw [← hdom]; exact hd
          refine ⟨(hab.2 σ hd').1, fun ξ hξ hξσ f hf => ?_⟩
          rw [fundBig_om_lim hreg] at hf
          rcases fr_om_sc hm hf with hf | hf
          · exact (hab.2 σ hd').2 ξ hξ hξσ f hf
          · rw [hf]; exact hd1
      · by_cases hed : e = d
        · rw [hed, omegaFixed_of_IsOF hOF] at heOF; cases heOF
        · exact IH.dd heM hed hOF hl hbot (fun f hf => h0 f (h0e f hf))
  | Xi n a =>
    have hTM : Lt (.Xi n a) (.M m) := by
      rcases triY hT hMF with h | e | h
      · exact h
      · cases e
      · exfalso
        have hl : m + 1 ≤ n := by have := lev_le_of_lt_gen h; simpa [lev] using this
        exact Lt.asymmY hT hSF hTS (succM_lt_xi hm hT hl)
    have hdT' : d = .Xi n a := by simpa [fr, hTM] using hdT
    rw [hdT']
    exact frConc_self hm hT hTM (by rw [← hdT']; exact hd1) (Or.inl ⟨n, a, rfl⟩)
  | Psi κ a =>
    rcases triY hT hMF with hTM | e | hMT
    · have hdT' : d = .Psi κ a := by simpa [fr, hTM] using hdT
      rw [hdT']
      exact frConc_self hm hT hTM (by rw [← hdT']; exact hd1) (Or.inr ⟨κ, a, rfl⟩)
    · cases e
    obtain ⟨Y, hY⟩ := prin_between_M hm hT rfl hMT hTS
    obtain ⟨rfl, rfl⟩ := Tm.Psi.inj hY.symm
    have hnlt : ¬ Lt (.Psi (succM m) Y) (.M m) := Lt.asymmY hMF hT hMT
    have hYF := hT.psi.aF
    have hTC' : inC Y (succM m) (.M m) = true ∧ Lt Y (succM m) := by
      rw [inC_psi] at hTC
      have h1 : (cmp (Tm.Psi (succM m) Y) (.M m) == .lt) = false := by
        rw [beq_eq_false_iff_ne]; exact hnlt
      rw [h1, Bool.false_or, Bool.and_eq_true, Bool.and_eq_true] at hTC
      exact ⟨hTC.1.2, beq_iff_eq.mp hTC.2⟩
    have hdY : d ∈ fr (.M m) Y := by
      rcases fr_psiS hm hT d hdT with e | h
      · exact absurd e hd1'
      · exact h
    by_cases hY0 : Y = .zero
    · subst hY0; simp [fr] at hdY
    by_cases hYs : isSucc Y = true
    · -- `T[n] = Ψ(Y-1)·(n+2)`：0 番目に `d` がある
      apply vac
      have hcs : cs (succM m) Y = .mul (.Psi (succM m) (pred Y)) 2 := cs_succ_om hYF hYs
      have hdom : dom (.Psi (succM m) Y) = .omega := by rw [dom_psi, hcs]; rfl
      have hf0 : fund (.Psi (succM m) Y) .zero = mulNat (.Psi (succM m) (pred Y)) 2 := by
        rw [fund_zero_omega hdom, fundNat_psi, hcs]; rfl
      have hT0F : WNF (mulNat (.Psi (succM m) (pred Y)) 2) := by rw [← hf0]; exact wnf_f0 hT
      have hBmem : Tm.Psi (succM m) (pred Y) ∈ summands (mulNat (.Psi (succM m) (pred Y)) 2) := by
        rw [summands_mulNat rfl]; simp
      have hBF := (summands_WNF _ hT0F _ hBmem).1
      have hdp : d ∈ fr (.M m) (pred Y) := by
        obtain ⟨ys, hys⟩ := summands_of_isSucc hYs
        obtain ⟨u, hu, hdu⟩ := mem_fr_iff.mp hdY
        rw [hys] at hu
        rcases List.mem_append.mp hu with hu | hu
        · exact mem_fr_iff.mpr ⟨u, by
            rw [show pred Y = predT Y from rfl, summands_predT hYF hys]; exact hu, hdu⟩
        · rw [List.mem_singleton.mp hu] at hdu; exact absurd (fr_M_one hm d hdu) hd1'
      rw [hf0]
      exact fr_of_mem_summands hBmem (fr_psiS_rev hm hBF hdp)
    -- `Y` は極限：最後の加数 `Ra` の近似
    obtain ⟨pa, Ra, hsa⟩ : ∃ pa Ra, summands Y = pa ++ [Ra] :=
      ⟨_, _, (List.dropLast_concat_getLast (summands_ne_nil hY0)).symm⟩
    have hNa : NFL (pa ++ [Ra]) := by rw [← hsa]; exact nfl_summands hYF
    have hRaW := hNa.1 Ra (by simp)
    have hRaF := hRaW.1
    have hRaq : Ra ∈ summands Y := by rw [hsa]; simp
    have hRas : ¬ isSucc Ra = true := by rw [← isSucc_of_last hsa hRaW.2]; exact hYs
    have hRa0 : Ra ≠ .zero := by intro e; rw [e] at hRaW; cases hRaW.2
    have hRaS : Lt Ra (succM m) :=
      lt_of_le_of_ltY hRaF hYF hSF (le_of_mem_summands hYF hRaq) hTC'.2
    have hcs := cs_succM_lim hYF hsa hYs hTC'.2 hm
    have hdomRa : ∀ σ, dom Ra = .big σ → dom (.Psi (succM m) Y) = .big σ := fun σ e => by
      rw [dom_psi, hcs]
      have hB := (inv_of Ra hRaF).2 σ e
      exact app_psi00_big_dom e (lt_of_le_of_ltY hB.props.σF hRaF hSF hB.σle hRaS)
    have hdomRaN : dom Ra = .omega → dom (.Psi (succM m) Y) = .omega := fun e => by
      rw [dom_psi, hcs]; exact app_psi00_dom_nat e
    have hRa0F := wnf_f0 hRaF
    have hRa0lt := f0_lt hRaF hRa0
    have hf0 : fund (.Psi (succM m) Y) .zero =
        .Psi (succM m) (oadd (ofSummands pa) (fund Ra .zero)) := by
      cases e : dom Ra with
      | zero => exact absurd ((dom_eq_zero_iff hRaF).mp e) hRa0
      | one => exact absurd ((dom_eq_one_iff hRaF).mp e) hRas
      | omega =>
        have hx : WNF ((info Ra).seq.nat 0) := by
          have := hRa0F; rw [fund_zero_omega e] at this; exact this
        rw [fund_zero_omega (hdomRaN e), fundNat_psi, hcs, app_psi00_nat e hx, fund_zero_omega e]
        rfl
      | big σ =>
        have hx : WNF ((info Ra).seq.big .zero) := by
          have := hRa0F; rw [fund_zero_big e] at this; exact this
        rw [fund_zero_big (hdomRa σ e), fundBig_psi, hcs, app_psi00_big hx, fund_zero_big e]
        rfl
    have hT0F : WNF (.Psi (succM m) (oadd (ofSummands pa) (fund Ra .zero))) := by
      rw [← hf0]; exact wnf_f0 hT
    have hsum0 : summands (oadd (ofSummands pa) (fund Ra .zero)) = pa ++ summands (fund Ra .zero) :=
      summands_oadd_pre (pre := pa) hNa hRa0F hRa0lt
    have hin0 : ∀ u f, u ∈ pa ++ summands (fund Ra .zero) → f ∈ fr (.M m) u →
        f ∈ fr (.M m) (fund (.Psi (succM m) Y) .zero) := by
      intro u f hu hf
      rw [hf0]
      exact fr_psiS_rev hm hT0F (fr_of_mem_summands (by rw [hsum0]; exact hu) hf)
    obtain ⟨u, hu, hdu⟩ := mem_fr_iff.mp hdY
    rw [hsa] at hu
    rcases List.mem_append.mp hu with hu | hu
    · exact vac _ (hin0 u d (List.mem_append_left _ hu) hdu)
    rw [List.mem_singleton.mp hu] at hdu
    -- `d` は `Ra` の前線
    have hRaC : inC Ra (succM m) (.M m) = true := inC_of_mem_summands hYF hTC'.1 hRaq
    have hfrRa : ∀ f, f ∈ fr (.M m) Ra → Le f d := fun f hf =>
      hfrT f (fr_psiS_rev hm hT (fr_of_mem_summands hRaq hf))
    have IH := ih Ra (by
      have := size_le_of_mem_subs (mem_subs_of_mem_summands hRaq)
      simp only [Tm.size]; omega) hRaF hRaS hRaC hdu hfrRa
    have h0R : ∀ f, f ∈ fr (.M m) (fund Ra .zero) → f ∈ fr (.M m) (fund (.Psi (succM m) Y) .zero) :=
      fun f hf => by
        obtain ⟨v, hv, hfv⟩ := mem_fr_iff.mp hf
        exact hin0 v f (List.mem_append_right _ hv) hfv
    have hfrk : ∀ x f, WNF x → Lt x Ra → WNF (.Psi (succM m) (oadd (ofSummands pa) x)) →
        f ∈ fr (.M m) (.Psi (succM m) (oadd (ofSummands pa) x)) →
        f = one ∨ (∃ u, u ∈ pa ∧ f ∈ fr (.M m) u) ∨ f ∈ fr (.M m) x := by
      intro x f hx hxR hW hf
      rcases fr_psiS hm hW f hf with e | hf
      · exact Or.inl e
      · obtain ⟨v, hv, hfv⟩ := mem_fr_iff.mp hf
        rw [summands_oadd_pre (pre := pa) hNa hx hxR] at hv
        rcases List.mem_append.mp hv with hv | hv
        · exact Or.inr (Or.inl ⟨v, hv, hfv⟩)
        · exact Or.inr (Or.inr (mem_fr_iff.mpr ⟨v, hv, hfv⟩))
    refine ⟨fun h0 => ?_, fun A hA h0 => IH.c A hA (fun f hf => h0 f (h0R f hf)),
      fun hTM => absurd hTM hnlt⟩
    have hab := IH.ab (fun f hf => h0 f (h0R f hf))
    have hpa : ∀ u f, u ∈ pa → f ∈ fr (.M m) u → Lt f d := fun u f hu hf =>
      h0 f (hin0 u f (List.mem_append_left _ hu) hf)
    refine ⟨fun hd n f hf => ?_, fun σ hd => ?_⟩
    · have hRd : dom Ra = .omega := by
        cases e : dom Ra with
        | zero => exact absurd ((dom_eq_zero_iff hRaF).mp e) hRa0
        | one => exact absurd ((dom_eq_one_iff hRaF).mp e) hRas
        | omega => rfl
        | big σ => rw [hdomRa σ e] at hd; cases hd
      have hRN := (props_all Ra hRaF).1 hRd
      have hxF := hRN.nf n
      have hxR := hRN.lt n
      have hTn : fundNat (.Psi (succM m) Y) n =
          .Psi (succM m) (oadd (ofSummands pa) (fundNat Ra n)) := by
        rw [fundNat_psi, hcs]; exact app_psi00_nat hRd hxF
      have hWn : WNF (.Psi (succM m) (oadd (ofSummands pa) (fundNat Ra n))) := by
        rw [← hTn]; exact ((props_all _ hT).1 hd).nf n
      rw [hTn] at hf
      rcases hfrk _ f hxF hxR hWn hf with e | ⟨u, hu, hfu⟩ | hf
      · rw [e]; exact hd1
      · exact hpa u f hu hfu
      · exact hab.1 hRd n f hf
    · have hRd : dom Ra = .big σ := by
        cases e : dom Ra with
        | zero => exact absurd ((dom_eq_zero_iff hRaF).mp e) hRa0
        | one => exact absurd ((dom_eq_one_iff hRaF).mp e) hRas
        | omega => rw [hdomRaN e] at hd; cases hd
        | big σ' => rw [hdomRa σ' e] at hd; cases hd; rfl
      refine ⟨(hab.2 σ hRd).1, fun ξ hξ hξσ f hf => ?_⟩
      have hRB := (props_all Ra hRaF).2 σ hRd
      have hxF := hRB.nf ξ hξ hξσ
      have hxR := hRB.lt ξ hξ hξσ
      have hTξ : fundBig (.Psi (succM m) Y) ξ =
          .Psi (succM m) (oadd (ofSummands pa) (fundBig Ra ξ)) := by
        rw [fundBig_psi, hcs]; exact app_psi00_big hxF
      have hWξ : WNF (.Psi (succM m) (oadd (ofSummands pa) (fundBig Ra ξ))) := by
        rw [← hTξ]; exact ((props_all _ hT).2 σ hd).nf ξ hξ hξσ
      rw [hTξ] at hf
      rcases hfrk _ f hxF hxR hWξ hf with e | ⟨u, hu, hfu⟩ | hf
      · rw [e]; exact hd1
      · exact hpa u f hu hfu
      · exact (hab.2 σ hRd).2 ξ hξ hξσ f hf

end MahloOCF.FS
