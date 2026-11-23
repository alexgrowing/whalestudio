import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeierstrassCoeffsIntegralAverageChangeOfVariable
import Development.AbelianVarietyTheory.Definitions.Divisors.DatumOfIsIntegersLattice
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.MulStableIntegral
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsDiscreteValuationRingValuationSubringAtPrime
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.AddMonoidHomEqZeroOfEventually
open NumberField IsDedekindDomain WeierstrassCurve GlobalTheory GlobalTheory.Published GlobalTheory.CMModel Formalism.L2.Th1.F
open scoped IntermediateField BigOperators Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weierstrassCoeffs_integral_average_change_of_variables : ∀ (V : ValuationSubring ℂ) (a₄ a₆ r s t : ℂ) (u : ℂˣ) (ι : Type) [Fintype ι] (X Y : ι → ℂ), IntV V ((⟨u, r, s, t⟩ : VariableChange ℂ) • (⟨0, 0, 0, a₄, a₆⟩ : WeierstrassCurve ℂ)) → V.valuation (Fintype.card ι : ℂ) = 1 → (∀ i, (X i - r) / (u : ℂ) ^ 2 ∈ V) → (∀ i, (Y i - t - s * (X i - r)) / (u : ℂ) ^ 3 ∈ V) → (∀ i, V.valuation (2 * Y i) = V.valuation (u : ℂ) ^ 3) → IntV V ((⟨u, (∑ i, X i) / Fintype.card ι, (∑ i, (3 * X i ^ 2 + a₄) / (2 * Y i)) / Fintype.card ι, (∑ i, Y i) / Fintype.card ι⟩ : VariableChange ℂ) • (⟨0, 0, 0, a₄, a₆⟩ : WeierstrassCurve ℂ)) := by
  first | exact @GlobalTheory.CMModel.intV_average | exact GlobalTheory.CMModel.intV_average | (intros; apply GlobalTheory.CMModel.intV_average <;> assumption)
