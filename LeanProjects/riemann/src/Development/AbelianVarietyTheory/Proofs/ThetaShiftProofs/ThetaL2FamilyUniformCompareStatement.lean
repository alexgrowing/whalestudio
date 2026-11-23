import Mathlib
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ThetaL2FamilyUniformCompare
import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsThetaL2NormSquared
import Development.AbelianVarietyTheory.Definitions.RegularCharts.ModelAt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree Formalism.L2.Pj.QAt GlobalTheory.ArcQ GlobalTheory.Frames
open scoped LaurentSeries
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.theta_l2_family_uniform_compare : Out.Laws → Out.Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (σ : c.F →+* ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (Fu : FamilyUnif Xo (σ.comp (IntermediateField.inclusion c.le).toRingHom) ty) (i i' : Fin Fu.n) (Pm : (Fu.Di i).La →+ (Fin g → ℂ)) (Pm' : (Fu.Di i').La →+ (Fin g → ℂ)) (y y' : FrPt Xo c (CAt σ)) (G : ∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) (CAt σ)) (s : CAt σ) (v v' : ℝ), IsPeriod (Fu.Di i) ty Pm → IsPeriod (Fu.Di i') ty Pm' → y.x = Fu.u i Pm → y'.x = Fu.u i' Pm' → FrChg G s y y' → IsThetaL2NormSquared Fu i Pm y v → IsThetaL2NormSquared Fu i' Pm' y' v' → 0 < v ∧ v' = ‖toC s‖ ^ 2 * v := by
  first | exact @GlobalTheory.GeneratorNorm.theta_l2_positive_and_scaling | exact GlobalTheory.GeneratorNorm.theta_l2_positive_and_scaling | (intros; apply GlobalTheory.GeneratorNorm.theta_l2_positive_and_scaling <;> assumption)
