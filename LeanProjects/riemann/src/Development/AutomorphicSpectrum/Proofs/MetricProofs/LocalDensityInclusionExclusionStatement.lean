import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.LocalDensityInclusionExclusion
import Mathlib
import ReciprocityTheory.AnalyticForms.LeviForms.ConvExpandStatement
open MeasureTheory Metric Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.AnForm.M.FinHolAtlas
open scoped ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_density_inclusion_exclusion : ∀ {e : ℕ} {X : Type} [TopologicalSpace X] (A : FinHolAtlas e X) (U : Set X) (P : Fin e → LocPot X) (f : Fin e → X → ℝ) (Θ : LocPot X), IsOpen U → (∀ i, IsPotential A (P i)) → IsPotential A Θ → (∀ i, A.SmoothOn U (f i)) → ∀ j, ∀ y ∈ (A.chart j).target ∩ (A.chart j).symm ⁻¹' U, locDens A (fun i => P i + LocPot.ofFun (f i)) j y = ∑ T : Finset (Fin e), (-1 : ℝ) ^ (e - T.card) * locDens A (fun i => (if i ∈ T then P i else LocPot.ofFun 0) + LocPot.ofFun (if i ∈ T then f i else 0) + Θ) j y := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Giv.locDens_expand_ofFun | exact GlobalTheory.CompanionTheory.Ar.Giv.locDens_expand_ofFun | (intros; apply GlobalTheory.CompanionTheory.Ar.Giv.locDens_expand_ofFun <;> assumption)
