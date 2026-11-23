import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsAlgClosureEmbeddingExtendingOnAlgebraic
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Formalism.PairingDivisors.StatementH
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.PderivIterEqPderivListOfDifferentiableOn
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsTraceCompatibleTorusEmbeddingStandardTorus
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.ThetaConj
open scoped BigOperators
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_algClosure_embedding_extending_on_algebraic : ∀ (M : IntermediateField ℚ ℂ) (ρ : M →ₐ[ℚ] ℂ), ∃ ρ' : Qbar →ₐ[ℚ] ℂ, ∀ x : ℂ, x ∈ Qbar → x ∈ M → cj M ρ x = cj Qbar ρ' x := by
  first | exact @GlobalTheory.ThetaConj.exists_cj_Qbar_eq | exact GlobalTheory.ThetaConj.exists_cj_Qbar_eq | (intros; apply GlobalTheory.ThetaConj.exists_cj_Qbar_eq <;> assumption)
