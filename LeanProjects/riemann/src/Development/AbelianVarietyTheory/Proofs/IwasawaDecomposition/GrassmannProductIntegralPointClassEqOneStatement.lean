import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GrassmannProductIntegralPointClassEqOne
import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RootToFlag
open MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.GoodMetric GlobalTheory.LieBase GlobalTheory.GrassTop
open Classical

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.grassmannProductIntegral_pointClass_eq_one : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H), intGr H Dw (pointPoly H Dw) = 1 := by
  first | exact @GlobalTheory.GrassTop.intGr_pointPoly | exact GlobalTheory.GrassTop.intGr_pointPoly | (intros; apply GlobalTheory.GrassTop.intGr_pointPoly <;> assumption)
