import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.NormalizedDegreeOrthogonalSum
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsOrthFull
open GroundTheory.Heights₂.Heights NumberField TensorProduct ComplexAt GlobalTheory.CompanionTheory.Ar Matrix
open scoped BigOperators ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.normalized_degree_orthogonal_sum : ∀ (K : Type) [Field K] [NumberField K] (E : HermitianBundle.{0} K) (I : Type) [Fintype I] (F : I → Submodule (𝓞 K) E.carrier), (∀ a b, a ≠ b → OrthAt E (F a) (F b)) → E.normDegree (⨆ a, F a) = ∑ a, E.normDegree (F a) ∧ E.rank (⨆ a, F a) = ∑ a, E.rank (F a) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.OrthSum.normDegree_rank_iSup | exact GlobalTheory.CompanionTheory.Ar.OrthSum.normDegree_rank_iSup | (intros; apply GlobalTheory.CompanionTheory.Ar.OrthSum.normDegree_rank_iSup <;> assumption)
