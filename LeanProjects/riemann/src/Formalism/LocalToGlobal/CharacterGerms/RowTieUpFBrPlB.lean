import Formalism.LocalToGlobal.CharacterGerms.RowTieUpFBrS
import Formalism.LocalToGlobal.CharacterGerms.RowTieUpFBrPl

set_option autoImplicit false

noncomputable section

namespace Formalism.L2.FormalSeriesBounds

namespace UpFBr

open ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs

theorem placeSt_of_X (h : Pl.PlaceCriterionOfIdempotent) : PlaceSt := by
  intro l _ OE _ _ _ _ _ R _ _ _ _ _ hl hd d _ em h1 h2 h3
  obtain ⟨e, he1, he2, he3, iN, t, jj, hj, ht, b, hb⟩ := h l OE R hl hd d em h1 h2 h3
  exact ⟨⟨e, he1, he2, he3⟩, iN, t, jj, hj, ht, b, hb⟩

end UpFBr

end Formalism.L2.FormalSeriesBounds
