import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSqAddPrimeOddModThreeValuationOne
import Development.AbelianVarietyTheory.Definitions.Divisors.DatumOfIsIntegersLattice
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.MulStableIntegral
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsDiscreteValuationRingValuationSubringAtPrime
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.AddMonoidHomEqZeroOfEventually
open NumberField IsDedekindDomain WeierstrassCurve GlobalTheory GlobalTheory.Published GlobalTheory.CMModel Formalism.L2.Th1.F
open scoped IntermediateField BigOperators Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_sq_add_prime_odd_mod_three_valuation_one : ∀ (p : ℕ) (V : ValuationSubring ℂ), p.Prime → 3 < p → ∃ a N : ℕ, N = a ^ 2 + p ∧ Odd N ∧ N % 3 = 2 ∧ V.valuation (N : ℂ) = 1 := by
  first | exact @GlobalTheory.CMModel.exists_sq_add_prime_odd_mod_three_unit | exact GlobalTheory.CMModel.exists_sq_add_prime_odd_mod_three_unit | (intros; apply GlobalTheory.CMModel.exists_sq_add_prime_odd_mod_three_unit <;> assumption)
