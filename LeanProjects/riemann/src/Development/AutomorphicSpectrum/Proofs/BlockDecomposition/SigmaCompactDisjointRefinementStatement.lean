import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SigmaCompactDisjointRefinement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JoinCol
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PAreaMultiplicityWeight
open MeasureTheory ReciprocityTheory.L2DbarEstimates GlobalTheory.CompanionTheory.FSCrofton
open scoped ENNReal ComplexConjugate
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sigma_compact_disjoint_refinement : ∀ (X : Type) [TopologicalSpace X] [CompactSpace X] [T2Space X] [SecondCountableTopology X] (ι : Type) (S : ι → Set X), (∀ i, IsOpen (S i)) → (⋃ i, S i) = Set.univ → ∃ (m : ℕ) (l : Fin m → ι) (A : Fin m → Set X), Pairwise (Function.onFun Disjoint A) ∧ (⋃ t, A t) = Set.univ ∧ (∀ t, A t ⊆ S (l t)) ∧ ∀ t, IsSigmaCompact (A t) := by
  first | exact @GlobalTheory.CompanionTheory.CroftonPartition.exists_sigmaCompact_partition | exact GlobalTheory.CompanionTheory.CroftonPartition.exists_sigmaCompact_partition | (intros; apply GlobalTheory.CompanionTheory.CroftonPartition.exists_sigmaCompact_partition <;> assumption)
