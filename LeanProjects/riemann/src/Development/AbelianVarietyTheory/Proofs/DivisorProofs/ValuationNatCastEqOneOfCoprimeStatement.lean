import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValuationNatCastEqOneOfCoprime
import Development.AbelianVarietyTheory.Definitions.Divisors.DatumOfIsIntegersLattice
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.MulStableIntegral
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsDiscreteValuationRingValuationSubringAtPrime
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.AddMonoidHomEqZeroOfEventually
open NumberField IsDedekindDomain WeierstrassCurve GlobalTheory GlobalTheory.Published GlobalTheory.CMModel Formalism.L2.Th1.F
open scoped IntermediateField BigOperators Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.valuation_natCast_eq_one_or_of_coprime : ∀ (V : ValuationSubring ℂ) (a b : ℕ), Nat.Coprime a b → V.valuation (a : ℂ) = 1 ∨ V.valuation (b : ℂ) = 1 := by
  first | exact @GlobalTheory.CMModel.valuation_natCast_eq_one_of_coprime | exact GlobalTheory.CMModel.valuation_natCast_eq_one_of_coprime | (intros; apply GlobalTheory.CMModel.valuation_natCast_eq_one_of_coprime <;> assumption)
