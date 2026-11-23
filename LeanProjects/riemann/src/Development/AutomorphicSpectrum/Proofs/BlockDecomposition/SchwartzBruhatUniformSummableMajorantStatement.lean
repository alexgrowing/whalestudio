import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SchwartzBruhatUniformSummableMajorant
import Development.WeilBound.CoreStatements.AutomorphicKernels.EisensteinSeriesG2.RankOneEisenstein.Theta2Integral
open NumberField Matrix MeasureTheory Filter Topology
open scoped NumberField.AdeleRing
open PositivityTheory.EisRk1 GroundTheory.Global GroundTheory.Automorphic GroundTheory.Automorphic.Adele2 GroundTheory.Automorphic.GodementSection IdeleGroup

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.schwartz_bruhat_uniform_summable_majorant : ∀ {K : Type _} [Field K] [NumberField K], ∀ {F : (Fin 2 → 𝔸[K]) → ℂ} (hF : F ∈ schwartzBruhat2 K) {C : Set (GL (Fin 2) 𝔸[K])} (hC : IsCompact C), ∃ u : (Fin 2 → K) → ℝ, Summable u ∧ ∀ h ∈ C, ∀ ξ : Fin 2 → K,
      ‖F ((fun i ↦ algebraMap K 𝔸[K] (ξ i)) ᵥ* (h : Matrix (Fin 2) (Fin 2) 𝔸[K]))‖ ≤ u ξ := by
  first | exact @GlobalTheory.CompanionTheory.EisRk1Bound.exists_summable_bound_theta2 | exact GlobalTheory.CompanionTheory.EisRk1Bound.exists_summable_bound_theta2 | (intros; apply GlobalTheory.CompanionTheory.EisRk1Bound.exists_summable_bound_theta2 <;> assumption)
