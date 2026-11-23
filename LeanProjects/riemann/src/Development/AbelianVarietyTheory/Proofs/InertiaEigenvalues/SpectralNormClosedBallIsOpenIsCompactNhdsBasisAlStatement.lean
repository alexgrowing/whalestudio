import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SpectralNormClosedBallIsOpenIsCompactNhdsBasisAl
import Mathlib
open Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.spectralNorm_closedBall_isOpen_isCompact_nhds : ∀ (F : Type) [NontriviallyNormedField F] [IsUltrametricDist F] [CompleteSpace F] [LocallyCompactSpace F] (L : Type) [Field L] [Algebra F L] [FiniteDimensional F L] [TopologicalSpace L] [IsModuleTopology F L], IsOpen {y : L | spectralNorm F L y ≤ 1} ∧ IsCompact {y : L | spectralNorm F L y ≤ 1} ∧ ∀ U ∈ 𝓝 (0 : L), ∃ r : ℝ, 0 < r ∧ ∀ y : L, spectralNorm F L y < r → y ∈ U := by
  first | exact @GlobalTheory.spectralNorm_closedBall_isOpen_isCompact_nhds_basis | exact GlobalTheory.spectralNorm_closedBall_isOpen_isCompact_nhds_basis | (intros; apply GlobalTheory.spectralNorm_closedBall_isOpen_isCompact_nhds_basis <;> assumption)
