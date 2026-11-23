import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsNatDiagIffIsDiag

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LocM

namespace GlobalTheory.ShFam.Pad.RelDim

theorem smooth_XF {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
    {l : Level H} (Xo : Moduli Dw l) (c : Coeff l) :
    SmoothOfRelativeDimension Dw.dim (pullback.snd Xo.s (spMap (IntermediateField.inclusion c.le).toRingHom)) := by
  haveI := smoothOfRelativeDimension_isStableUnderBaseChange Dw.dim
  exact MorphismProperty.of_isPullback (IsPullback.of_hasPullback _ _) Xo.smooth

end GlobalTheory.ShFam.Pad.RelDim
