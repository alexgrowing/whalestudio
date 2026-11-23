import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValuationTwelfthPowerOfCube
import Development.AbelianVarietyTheory.Definitions.Divisors.DatumOfIsIntegersLattice
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.MulStableIntegral
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsDiscreteValuationRingValuationSubringAtPrime
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.AddMonoidHomEqZeroOfEventually
open NumberField IsDedekindDomain WeierstrassCurve GlobalTheory GlobalTheory.Published GlobalTheory.CMModel Formalism.L2.Th1.F
open scoped IntermediateField BigOperators Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_valuation_pow_twelve_mul_eq : ∀ (p : ℕ) (V : ValuationSubring ℂ) (F : IntermediateField ℚ ℂ) (D A Q : ℂ), p % 4 = 3 → D ∈ F → A ∈ F → Q ∈ F → D ≠ 0 → A ≠ 0 → V.valuation A ^ 3 = V.valuation D → Q ^ 8 * (p : ℂ) ^ 6 = D ^ (p - 1) → ∃ u ∈ F, u ≠ 0 ∧ V.valuation u ^ 12 * V.valuation (p : ℂ) ^ (if p % 8 = 3 then 3 else 9) = V.valuation D := by
  first | exact @GlobalTheory.valuation_twelfth_power_of_cube | exact GlobalTheory.valuation_twelfth_power_of_cube | (intros; apply GlobalTheory.valuation_twelfth_power_of_cube <;> assumption)
