import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NatCastNotMemCubePrimeAdjoinJInvariantSqrtNeg
import Development.AbelianVarietyTheory.Definitions.Divisors.DatumOfIsIntegersLattice
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.MulStableIntegral
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsDiscreteValuationRingValuationSubringAtPrime
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.AddMonoidHomEqZeroOfEventually
open NumberField IsDedekindDomain WeierstrassCurve GlobalTheory GlobalTheory.Published GlobalTheory.CMModel Formalism.L2.Th1.F
open scoped IntermediateField BigOperators Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.natCast_notMem_cube_prime_adjoin_jInvariant_sqrtNeg : ∀ (p : ℕ) (L₀ : PeriodPair) [NumberField ℚ⟮(latticeCurve L₀).j⟯] (w : HeightOneSpectrum (𝓞 ℚ⟮(latticeCurve L₀).j⟯)), p.Prime → IsIntegersLattice p L₀ → (p : 𝓞 ℚ⟮(latticeCurve L₀).j⟯) ∉ w.asIdeal ^ 3 := by
  first | exact @GlobalTheory.CMModel.natCast_notMem_pow_three_adjoin_j | exact GlobalTheory.CMModel.natCast_notMem_pow_three_adjoin_j | (intros; apply GlobalTheory.CMModel.natCast_notMem_pow_three_adjoin_j <;> assumption)
