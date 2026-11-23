import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIntVVariableChange
import Development.AbelianVarietyTheory.Definitions.Divisors.DatumOfIsIntegersLattice
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.MulStableIntegral
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsDiscreteValuationRingValuationSubringAtPrime
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.AddMonoidHomEqZeroOfEventually
open NumberField IsDedekindDomain WeierstrassCurve GlobalTheory GlobalTheory.Published GlobalTheory.CMModel Formalism.L2.Th1.F
open scoped IntermediateField BigOperators Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_variableChange_intV_of_j_mem : ∀ (W : WeierstrassCurve ℂ) [W.IsElliptic] (V : ValuationSubring ℂ) (u : ℂˣ), W.j ∈ V → V.valuation (u : ℂ) ^ 12 = V.valuation W.Δ → ∃ r s t : ℂ, IntV V ((⟨u, r, s, t⟩ : VariableChange ℂ) • W) := by
  first | exact @GlobalTheory.CMModel.exists_intV_variableChange | exact GlobalTheory.CMModel.exists_intV_variableChange | (intros; apply GlobalTheory.CMModel.exists_intV_variableChange <;> assumption)
