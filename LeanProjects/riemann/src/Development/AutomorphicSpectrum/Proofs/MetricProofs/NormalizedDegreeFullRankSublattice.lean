import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsOrthFull
import Development.WeilBound.CoreStatements.AmpleLineBundles.NormDegreeFullRankSubmoduleBounds
open GroundTheory.Heights₂.Heights NumberField TensorProduct ComplexAt GlobalTheory.CompanionTheory.Ar Matrix
open scoped BigOperators ComplexOrder

namespace GlobalTheory.CompanionTheory.Ar.IndexBound

theorem full_sublattice_normDegree_bounds : ∀ (K : Type) [Field K] [NumberField K] (E : HermitianBundle.{0} K) (F : Submodule (𝓞 K) E.carrier), E.rank F = Module.finrank (𝓞 K) E.carrier → E.normDegree F ≤ E.normDegree ⊤ ∧ ∀ d : ℤ, d ≠ 0 → (∀ x : E.carrier, d • x ∈ F) → E.normDegree ⊤ ≤ E.normDegree F + Module.finrank (𝓞 K) E.carrier * Real.log |(d : ℝ)| := by
  exact @CoverDenseAlt.normDegree_full_rank_submodule_bounds

end GlobalTheory.CompanionTheory.Ar.IndexBound
