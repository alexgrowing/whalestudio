import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.RefineAdaptedAtlasWithGradient
import Mathlib
import ReciprocityTheory.AnalyticForms.LeviForms.RegGlue
import ReciprocityTheory.AnalyticForms.LeviForms.RegChartC
import ReciprocityTheory.AnalyticForms.LeviForms.TailCut
open MeasureTheory Metric Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.AnForm.M.FinHolAtlas
open scoped ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.refine_adapted_atlas_with_gradient : ∀ {e : ℕ} {X : Type} [TopologicalSpace X] [CompactSpace X] [T2Space X] (A B : FinHolAtlas e X) (L th : LocPot X) (s : X → X → ℂ) (ph : X → ℝ) (C₅ : ℝ), (∀ y, logNormSec L s y ≤ 0) → IsAdaptedAtlas A B L s → IsGradBound B L s ph C₅ → ∃ (B' : FinHolAtlas e X) (x : Fin B'.n → X), IsAdaptedAtlas A B' L s ∧ IsGradBound B' L s ph |C₅| ∧ ∀ j, (B'.chart j).source ⊆ th.U (x j) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Giv.refine_adapted_atlas | exact GlobalTheory.CompanionTheory.Ar.Giv.refine_adapted_atlas | (intros; apply GlobalTheory.CompanionTheory.Ar.Giv.refine_adapted_atlas <;> assumption)
