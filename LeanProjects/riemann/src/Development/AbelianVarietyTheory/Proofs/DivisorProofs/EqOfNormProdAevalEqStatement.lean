import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOfNormProdAevalEq
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDimEqOne
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eq_of_norm_prod_aeval_eq' : ∀ (l : ℕ) [Fact l.Prime] (P Q : Polynomial ℚ_[l]), P.Monic → Q.Monic → P.natDegree = Q.natDegree → (∀ F : Polynomial ℤ, ‖((P.aroots (PadicAlgCl l)).map (fun a => Polynomial.aeval a F)).prod‖ = ‖((Q.aroots (PadicAlgCl l)).map (fun a => Polynomial.aeval a F)).prod‖) → P = Q := by
  first | exact @GlobalTheory.PadicRootNorm.eq_of_norm_prod_aeval_eq | exact GlobalTheory.PadicRootNorm.eq_of_norm_prod_aeval_eq | (intros; apply GlobalTheory.PadicRootNorm.eq_of_norm_prod_aeval_eq; all_goals assumption)
