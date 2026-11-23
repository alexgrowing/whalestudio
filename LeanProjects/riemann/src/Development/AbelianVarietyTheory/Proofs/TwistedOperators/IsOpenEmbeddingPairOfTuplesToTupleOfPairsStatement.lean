import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsOpenEmbeddingPairOfTuplesToTupleOfPairs
import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MulVecCEApply
import Development.AbelianVarietyTheory.Definitions.Foundations.T2SpaceTensorProductFiniteExtension
open MeasureTheory Topology Matrix NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx GlobalTheory.ModuLR
open scoped NNReal ENNReal TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isOpenEmbedding_pairOfTuplesToTupleOfPairs : ∀ (κ X Y : Type) [Fintype κ] [AddCommGroup X] [TopologicalSpace X] [AddCommGroup Y] [TopologicalSpace Y], IsOpenEmbedding (zipHom κ X Y) := by
  first | exact @GlobalTheory.ModuLR.zipHom_isOpenEmbedding | exact GlobalTheory.ModuLR.zipHom_isOpenEmbedding | (intros; apply GlobalTheory.ModuLR.zipHom_isOpenEmbedding <;> assumption)
