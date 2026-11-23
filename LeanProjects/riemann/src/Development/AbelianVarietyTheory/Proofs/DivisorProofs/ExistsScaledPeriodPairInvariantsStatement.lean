import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsScaledPeriodPairInvariants
import Development.AbelianVarietyTheory.Definitions.Divisors.DatumOfIsIntegersLattice
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.MulStableIntegral
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsDiscreteValuationRingValuationSubringAtPrime
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.AddMonoidHomEqZeroOfEventually
open NumberField IsDedekindDomain WeierstrassCurve GlobalTheory GlobalTheory.Published GlobalTheory.CMModel Formalism.L2.Th1.F
open scoped IntermediateField BigOperators Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_scaled_periodPair_invariants : ∀ (L : PeriodPair) (c : ℂ), c ≠ 0 → ∃ L' : PeriodPair, (∀ z, c * z ∈ L'.lattice ↔ z ∈ L.lattice) ∧ L'.g₂ = (c ^ 4)⁻¹ * L.g₂ ∧ L'.g₃ = (c ^ 6)⁻¹ * L.g₃ ∧ (∀ z, L'.derivWeierstrassP (c * z) = (c ^ 3)⁻¹ * L.derivWeierstrassP z) ∧ (latticeCurve L').j = (latticeCurve L).j := by
  first | exact @GlobalTheory.CMModel.exists_scaled_periodPair | exact GlobalTheory.CMModel.exists_scaled_periodPair | (intros; apply GlobalTheory.CMModel.exists_scaled_periodPair <;> assumption)
