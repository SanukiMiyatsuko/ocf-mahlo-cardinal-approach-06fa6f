import Mahlo.FS.Props
import Mahlo.FS.Below

/-! `Ξ_n(d)` の列の始点 `Ψ_{Ξ_n(d)}(d+1)` は標準形（`wnf_base_xi`）。

標準形の条件 `d+1 ∈ C(d+1, Ψ_{Ξ_n(d)}(d+1))` は、`d ∈ C(d, Ξ_n(d))`（`xi_selfY`）から、`d` の部分項で
`Ξ_n(d)` 未満のものが `Ψ_{Ξ_n(d)}(d+1)` 未満であること（`sub_lt_psi`）で移す。 -/

namespace MahloOCF.FS

open Tm

/-- `d` の部分項で `Ξ_n(d)` 未満のものは、どの `A` についても `Ψ_{Ξ_n(d)}(A)` 未満 -/
theorem sub_lt_base_xi {n : Nat} {d : Tm} (h : WNF (.Xi n d)) (A : Tm) : ∀ u, u ∈ subs d → WNF u →
    Lt u (.Xi n d) → Lt u (.Psi (.Xi n d) A) :=
  fun u hu huF hlt => sub_lt_psi h (Or.inr (Or.inr ⟨n, d, rfl⟩)) A u (subs_xi hu)
    (ne_of_size_lt (by have := size_le_of_mem_subs hu; simp only [Tm.size]; omega)) huF hlt

/-- `c` の部分項で `Ω_c` 未満のものは、どの `A` についても `Ψ_{Ω_c}(A)` 未満 -/
theorem sub_lt_base_om {c : Tm} (h : WNF (.Om c)) (hs : omReg c) (A : Tm) : ∀ u, u ∈ subs c → WNF u →
    Lt u (.Om c) → Lt u (.Psi (.Om c) A) :=
  fun u hu huF hlt => sub_lt_psi h (isTgt_of_omReg hs) A u (subs_om hu)
    (ne_of_size_lt (by have := size_le_of_mem_subs hu; simp only [Tm.size]; omega)) huF hlt

/-- `Ξ_n(d)` の列の始点 `Ψ_{Ξ_n(d)}(d+1)` は標準形 -/
theorem wnf_base_xi {n : Nat} {d : Tm} (h : WNF (.Xi n d)) : WNF (base (.Xi n d)) := by
  have hdF := h.xi.2.1
  have hsd := succT_WNF hdF
  show WNF (.Psi (.Xi n d) (sc d))
  refine WNF.mk_psi ⟨Or.inr (Or.inr ⟨n, d, rfl⟩), h, hsd, fun _ _ e => by cases e; exact lt_succT d, ?_⟩
  refine inC_succT (inC_one (succT_ne_zero d)) ?_
  refine inC_mono_node d d (.Xi n d) (succT d) _ (xi_selfY h)
    (fun v hv _ hvlt => sub_lt_base_xi h _ v hv (hdF.of_mem_subs hv) hvlt)
    (fun v hv _ hvd => lt_transY (hdF.of_mem_subs hv) hdF hsd hvd (lt_succT d))

end MahloOCF.FS
