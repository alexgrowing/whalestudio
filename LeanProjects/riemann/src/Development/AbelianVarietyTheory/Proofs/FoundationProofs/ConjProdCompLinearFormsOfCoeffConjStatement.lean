import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ConjProdCompLinearFormsOfCoeffConj
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Formalism.PairingDivisors.StatementH
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.PderivIterEqPderivListOfDifferentiableOn
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsTraceCompatibleTorusEmbeddingStandardTorus
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.ThetaConj
open scoped BigOperators
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.conj_prod_comp_linearForms_of_coeff_conj : ∀ (D : D7) (N N' r : ℕ) (M : IntermediateField ℚ ℂ) (ρ : M →ₐ[ℚ] ℂ) (g g' : Fin r → ℂ → ℂ) (l l' : Fin r → VC D N N'), (∀ j, Differentiable ℂ (g j)) → (∀ j, Differentiable ℂ (g' j)) → (∀ j n, coef1 (g j) n ∈ M ∧ coef1 (g' j) n = cj M ρ (coef1 (g j) n)) → (∀ j τ a c, l j τ a c ∈ M ∧ l' j τ a c = cj M ρ (l j τ a c)) → CjF D M ρ (fun z : VC D N N' => ∏ j, g j (∑ τ, ∑ a, ∑ c, z τ a c * l j τ a c)) (fun z : VC D N N' => ∏ j, g' j (∑ τ, ∑ a, ∑ c, z τ a c * l' j τ a c)) := by
  first | exact @GlobalTheory.ThetaConj.ProdLin.cjF_prod | exact GlobalTheory.ThetaConj.ProdLin.cjF_prod | (intros; apply GlobalTheory.ThetaConj.ProdLin.cjF_prod <;> assumption)
