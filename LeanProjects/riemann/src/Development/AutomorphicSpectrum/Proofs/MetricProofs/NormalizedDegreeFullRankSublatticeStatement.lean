import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.NormalizedDegreeFullRankSublattice
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsOrthFull
open GroundTheory.Heights₂.Heights NumberField TensorProduct ComplexAt GlobalTheory.CompanionTheory.Ar Matrix
open scoped BigOperators ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.normalized_degree_full_rank_sublattice : ∀ (K : Type) [Field K] [NumberField K] (E : HermitianBundle.{0} K) (F : Submodule (𝓞 K) E.carrier), E.rank F = Module.finrank (𝓞 K) E.carrier → E.normDegree F ≤ E.normDegree ⊤ ∧ ∀ d : ℤ, d ≠ 0 → (∀ x : E.carrier, d • x ∈ F) → E.normDegree ⊤ ≤ E.normDegree F + Module.finrank (𝓞 K) E.carrier * Real.log |(d : ℝ)| := by
  first | exact @GlobalTheory.CompanionTheory.Ar.IndexBound.full_sublattice_normDegree_bounds | exact GlobalTheory.CompanionTheory.Ar.IndexBound.full_sublattice_normDegree_bounds | (intros; apply GlobalTheory.CompanionTheory.Ar.IndexBound.full_sublattice_normDegree_bounds <;> assumption)
