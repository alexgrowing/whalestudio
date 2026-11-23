import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DatumOfIsIntegersLattice
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.MulStableIntegral
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsDiscreteValuationRingValuationSubringAtPrime
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.AddMonoidHomEqZeroOfEventually
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.HasSumLocallyUniformlyWeierstrassZetaExcept
open NumberField IsDedekindDomain WeierstrassCurve GlobalTheory GlobalTheory.Published GlobalTheory.CMModel Formalism.L2.Th1.F
open scoped IntermediateField BigOperators Topology

namespace GlobalTheory.CMModel

theorem exists_scaled_periodPair : ∀ (L : PeriodPair) (c : ℂ), c ≠ 0 → ∃ L' : PeriodPair,
    (∀ z, c * z ∈ L'.lattice ↔ z ∈ L.lattice) ∧ L'.g₂ = (c ^ 4)⁻¹ * L.g₂ ∧
      L'.g₃ = (c ^ 6)⁻¹ * L.g₃ ∧
      (∀ z, L'.derivWeierstrassP (c * z) = (c ^ 3)⁻¹ * L.derivWeierstrassP z) ∧
      (latticeCurve L').j = (latticeCurve L).j := by
  intro L c hc
  have hH : IsHomothetic c L (scalePeriods L c hc) := isHomothetic_scalePeriods L c hc
  have h2 : (scalePeriods L c hc).g₂ = (c ^ 4)⁻¹ * L.g₂ := by
    rw [PeriodPair.g₂, PeriodPair.g₂, hH.G_eq]; ring
  have h3 : (scalePeriods L c hc).g₃ = (c ^ 6)⁻¹ * L.g₃ := by
    rw [PeriodPair.g₃, PeriodPair.g₃, hH.G_eq]; ring
  refine ⟨scalePeriods L c hc, hH, h2, h3, hH.derivWeierstrassP_mul, ?_⟩
  have hi : (c ^ 12)⁻¹ ≠ 0 := inv_ne_zero (pow_ne_zero _ hc)
  have hD : (scalePeriods L c hc).g₂ ^ 3 - 27 * (scalePeriods L c hc).g₃ ^ 2 =
      (c ^ 12)⁻¹ * (L.g₂ ^ 3 - 27 * L.g₃ ^ 2) := by
    rw [h2, h3]; ring
  have hn : (scalePeriods L c hc).g₂ ^ 3 = (c ^ 12)⁻¹ * L.g₂ ^ 3 := by rw [h2]; ring
  rw [latticeCurve_j_eq, latticeCurve_j_eq, hD, hn, mul_left_comm, mul_div_mul_left _ _ hi]

end GlobalTheory.CMModel
