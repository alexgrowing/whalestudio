import Formalism.LocalToGlobal.ProjectiveLattices.FnTrdegOf
import Formalism.LocalToGlobal.ProjectiveLattices.KapTrdegPfB

noncomputable section

namespace Formalism.L2.Pj

open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}

set_option backward.isDefEq.respectTransparency.types false in
instance smoothOfRelativeDimension_strK (Xo : Moduli Dw l) (c : Coeff l) :
    SmoothOfRelativeDimension Dw.dim (strK (Xo := Xo) (c := c)) := by
  have := smoothOfRelativeDimension_isStableUnderBaseChange.{0} Dw.dim
  exact MorphismProperty.pullback_snd (P := @SmoothOfRelativeDimension Dw.dim) _ _ Xo.smooth

theorem kapTrdeg_pf (Xo : Moduli Dw l) (c : Coeff l) : KapTrdeg Xo c Dw.dim := by
  intro Z
  have h := @TranscendenceDegreeLemmas.trdeg_residueField_genericPoint c.F _ _ _ _
    (strK (Xo := Xo) (c := c)) Dw.dim _ _ Z.2 (algKap Z)
  exact h

theorem kapFG_pf (Xo : Moduli Dw l) (c : Coeff l) : KapFG Xo c := by
  intro Z
  have h := @TranscendenceDegreeLemmas.fg_residueField_genericPoint c.F _ _ _ _
    (strK (Xo := Xo) (c := c)) Dw.dim _ _ Z.2 (algKap Z)
  exact h

end Formalism.L2.Pj

end
