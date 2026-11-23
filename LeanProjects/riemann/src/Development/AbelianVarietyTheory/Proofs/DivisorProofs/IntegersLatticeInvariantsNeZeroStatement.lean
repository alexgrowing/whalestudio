import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegersLatticeInvariantsNeZero
import Development.AbelianVarietyTheory.Definitions.Divisors.DatumOfIsIntegersLattice
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.MulStableIntegral
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsDiscreteValuationRingValuationSubringAtPrime
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.AddMonoidHomEqZeroOfEventually
open NumberField IsDedekindDomain WeierstrassCurve GlobalTheory GlobalTheory.Published GlobalTheory.CMModel Formalism.L2.Th1.F
open scoped IntermediateField BigOperators Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integersLattice_g2_g3_ne_zero_and_mulStable : ∀ (p : ℕ) (L : PeriodPair), p.Prime → 3 < p → IsIntegersLattice p L → L.g₂ ≠ 0 ∧ L.g₃ ≠ 0 ∧ MulStable L (sqrtNegNat p) := by
  first | exact @GlobalTheory.CMModel.integersLattice_invariants_ne_zero | exact GlobalTheory.CMModel.integersLattice_invariants_ne_zero | (intros; apply GlobalTheory.CMModel.integersLattice_invariants_ne_zero <;> assumption)
