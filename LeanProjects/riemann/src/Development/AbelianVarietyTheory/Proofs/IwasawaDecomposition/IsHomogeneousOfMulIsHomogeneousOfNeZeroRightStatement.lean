import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsHomogeneousOfMulIsHomogeneousOfNeZeroRight
import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RootToFlag
open MvPolynomial NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.GoodMetric GlobalTheory.LieBase GlobalTheory.GrassTop
open Classical

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isHomogeneous_of_mul_isHomogeneous_of_ne_zero_right : ∀ {σ : Type} (P Q : MvPolynomial σ ℝ) (a b : ℕ), Q ≠ 0 → Q.IsHomogeneous b → (P * Q).IsHomogeneous (a + b) → P.IsHomogeneous a := by
  first | exact @GlobalTheory.GrassTop.isHomogeneous_of_mul_isHomogeneous_right | exact GlobalTheory.GrassTop.isHomogeneous_of_mul_isHomogeneous_right | (intros; apply GlobalTheory.GrassTop.isHomogeneous_of_mul_isHomogeneous_right <;> assumption)
