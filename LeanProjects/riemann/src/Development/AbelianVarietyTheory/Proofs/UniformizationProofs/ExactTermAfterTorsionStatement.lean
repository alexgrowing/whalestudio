import Mathlib
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExactTermAfterTorsion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ExistsZeroGt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DataRigidSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DvrLem
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ThetaVV
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.VRatioGtStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ValuationMultiplicationInvariance
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PeriodicValuation
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBC
import Development.AbelianVarietyTheory.Definitions.Uniformization.TXFrame
import Development.AbelianVarietyTheory.Definitions.Uniformization.AllDV
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT
theorem _root_.GlobalTheory.T.exists_nsmul_add_decomp_with_coef_valuation : LL → TwistBCSpanStatement → TWM.VRatioGtStatement → TWStatement → UUStatement → AllDV fun {V} _ _ _ {ϖ} hϖ D Q {F} _ _ {v} hv => ∀ ϑ : Fam D.toPre F 1, Prim D Q v ϑ → ∀ (n : ℕ), 2 ≤ n → IsUnit (n : V) → ∀ (g : GtPtF D.toPre F) (χ : D.toPre.X), ∃ (h o g₂ : GtPtF D.toPre F), o.IsZero ∧ GtPtF.IsNsmul n h o ∧ g.IsAdd h g₂ ∧ ∀ (w : Frm D.toPre F 1 g₂.b) l ω, w.IsGen → GtV hϖ hv g₂ l → GenV hϖ hv w ω → v (coef ϑ g₂ w χ) = (((Q χ : ℚ) + l χ + ω : ℚ) : WithTop ℚ) := by
  first | exact @GlobalTheory.UT.ExactTerm.exact_term_after_torsion | exact GlobalTheory.UT.ExactTerm.exact_term_after_torsion | (intros; apply GlobalTheory.UT.ExactTerm.exact_term_after_torsion <;> assumption)
