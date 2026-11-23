import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIntegralOfModelAt
import Development.AbelianVarietyTheory.Definitions.Divisors.DatumOfIsIntegersLattice
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.MulStableIntegral
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsDiscreteValuationRingValuationSubringAtPrime
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.AddMonoidHomEqZeroOfEventually
open NumberField IsDedekindDomain WeierstrassCurve GlobalTheory GlobalTheory.Published GlobalTheory.CMModel Formalism.L2.Th1.F
open scoped IntermediateField BigOperators Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_variableChange_isIntegral_of_modelAt : ∀ (F : IntermediateField ℚ ℂ) [NumberField F] (w : HeightOneSpectrum (𝓞 F)) (V : ValuationSubring ℂ) (A : WeierstrassCurve F) (D : F), (∀ x : F, (x : ℂ) ∈ V ↔ x ∈ w.valuationSubringAtPrime F) → D ≠ 0 → ModelAt V F (A.map (algebraMap F ℂ)) (D : ℂ) → ∃ (C : VariableChange F) (u : (w.valuationSubringAtPrime F)ˣ), (C • A).IsIntegral (w.valuationSubringAtPrime F) ∧ (C • A).Δ = ((u : w.valuationSubringAtPrime F) : F) * D := by
  first | exact @GlobalTheory.CMModel.exists_integral_of_modelAt | exact GlobalTheory.CMModel.exists_integral_of_modelAt | (intros; apply GlobalTheory.CMModel.exists_integral_of_modelAt <;> assumption)
