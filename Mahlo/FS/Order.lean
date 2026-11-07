import Mahlo.FS.Class
import Mahlo.WF.Wmax

/-! 標準形の型 `NF` と、その上の整列順序（`Well_Order`）。整礎性は `MahloOCF.wellFounded_isNF`。 -/

namespace MahloOCF.FS

/-- 標準形 -/
abbrev NF := {t : Tm // isNF t = true}

instance : LT NF := ⟨fun a b => Lt a.1 b.1⟩

instance : DecidableLT NF := fun a b => inferInstanceAs (Decidable (cmp a.1 b.1 = .lt))

instance : Well_Order NF where
  lt_trans a b c h1 h2 := lt_transY a.2 b.2 c.2 h1 h2
  lt_total a b := by
    rcases triY a.2 b.2 with h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inr (Subtype.ext h))
    · exact Or.inr (Or.inl h)
  lt_wf := wellFounded_isNF

end MahloOCF.FS
