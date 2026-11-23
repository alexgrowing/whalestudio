import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.SmoothOnOfChartLeviNonneg
import Mathlib
import ReciprocityTheory.AnalyticForms.LeviForms.RegGlue
import ReciprocityTheory.AnalyticForms.LeviForms.RegChartC
import ReciprocityTheory.AnalyticForms.LeviForms.TailCut
open MeasureTheory Metric Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.AnForm.M.FinHolAtlas
open scoped ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.smoothOn_of_chart_levi_nonneg : ∀ {e : ℕ} {X : Type} [TopologicalSpace X] (A B : FinHolAtlas e X) (th : LocPot X) (x₀ : X) (j : Fin B.n) (V : Set (Fin e → ℂ)) (g : (Fin e → ℂ) → ℝ), A.Compatible B → IsPotential A th → (B.chart j).source ⊆ th.U x₀ → IsOpen V → V ⊆ (B.chart j).target → ContDiffOn ℝ ∞ g V → (∀ z ∈ V, ∀ w : Fin e → ℂ, 0 ≤ levi (fun z' => th.φ x₀ ((B.chart j).symm z') + g z') z w) → A.SmoothOn ((B.chart j).source ∩ B.chart j ⁻¹' V) (g ∘ B.chart j) ∧ IsPshOn A ((B.chart j).source ∩ B.chart j ⁻¹' V) (th + LocPot.ofFun (g ∘ B.chart j)) := by
  first | exact @GlobalTheory.CompanionTheory.Metric.PshBack.smoothOn_isPshOn_chartBack | exact GlobalTheory.CompanionTheory.Metric.PshBack.smoothOn_isPshOn_chartBack | (intros; apply GlobalTheory.CompanionTheory.Metric.PshBack.smoothOn_isPshOn_chartBack <;> assumption)
