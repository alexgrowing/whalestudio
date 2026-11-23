import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CubicThreeRoots
import Development.AbelianVarietyTheory.Definitions.Divisors.DatumOfIsIntegersLattice
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.MulStableIntegral
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsDiscreteValuationRingValuationSubringAtPrime
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.AddMonoidHomEqZeroOfEventually
open NumberField IsDedekindDomain WeierstrassCurve GlobalTheory GlobalTheory.Published GlobalTheory.CMModel Formalism.L2.Th1.F
open scoped IntermediateField BigOperators Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cubic_factor_and_discriminant_of_three_distinct_roots : ∀ (g h e₁ e₂ e₃ : ℂ), 4 * e₁ ^ 3 - g * e₁ - h = 0 → 4 * e₂ ^ 3 - g * e₂ - h = 0 → 4 * e₃ ^ 3 - g * e₃ - h = 0 → e₁ ≠ e₂ → e₁ ≠ e₃ → e₂ ≠ e₃ → (∀ x, 4 * x ^ 3 - g * x - h = 4 * (x - e₁) * (x - e₂) * (x - e₃)) ∧ 16 * ((3 * e₁ ^ 2 - g / 4) * (3 * e₂ ^ 2 - g / 4) * (3 * e₃ ^ 2 - g / 4)) = -(g ^ 3 - 27 * h ^ 2) := by
  first | exact @GlobalTheory.CMModel.cubic_three_roots | exact GlobalTheory.CMModel.cubic_three_roots | (intros; apply GlobalTheory.CMModel.cubic_three_roots <;> assumption)
