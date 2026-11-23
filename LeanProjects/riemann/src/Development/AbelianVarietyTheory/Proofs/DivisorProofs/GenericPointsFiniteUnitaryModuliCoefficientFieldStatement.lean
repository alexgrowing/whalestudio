import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenericPointsFiniteUnitaryModuliCoefficientField
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UOver
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.ZH GlobalTheory.UPoinc GlobalTheory.UCovSep
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.genericPoints_finite_unitaryModuli_coefficientField : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l), (genericPoints (Xo.XF c)).Finite := by
  first | exact @GlobalTheory.XScov.genericPoints_XF_finite | exact GlobalTheory.XScov.genericPoints_XF_finite | (intros; apply GlobalTheory.XScov.genericPoints_XF_finite <;> assumption)
