import Mathlib
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.TendstoSublevelDensityProdMeasure
import Mathlib
import Formalism.LocalRingCardinality.DataCD
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.PerpendicularEmbedding
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ContinuousMatrixEntryAbsSum
open MeasureTheory Matrix Filter Topology Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.PerpendicularEmbedding GlobalTheory.CompactDualQuot
open scoped ENNReal NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tendsto_sublevel_density_prod_measure : ∀ (A₁ E₁ A₂ E₂ : Type) [MeasurableSpace A₁] [MeasurableSpace E₁] [MeasurableSpace A₂] [MeasurableSpace E₂] (m₁ : Measure A₁) (l₁ : Measure E₁) (m₂ : Measure A₂) (l₂ : Measure E₂) [SFinite m₁] [SFinite l₁] [SFinite m₂] [SFinite l₂] (n₁ : A₁ → ℝ) (N₁ : E₁ → ℝ) (n₂ : A₂ → ℝ) (N₂ : E₂ → ℝ) (c₁ c₂ : ℝ≥0∞), Measurable n₁ → Measurable N₁ → Measurable n₂ → Measurable N₂ → (∀ x, 0 ≤ n₁ x) → (∀ x, 0 ≤ N₁ x) → (∀ x, 0 ≤ n₂ x) → (∀ x, 0 ≤ N₂ x) → c₁ ≠ ⊤ → c₂ ≠ ⊤ → (∀ r : ℝ, 0 < r → l₁ {x | N₁ x < r} ≠ 0 ∧ l₁ {x | N₁ x < r} ≠ ⊤) → (∀ r : ℝ, 0 < r → l₂ {x | N₂ x < r} ≠ 0 ∧ l₂ {x | N₂ x < r} ≠ ⊤) → Tendsto (fun r : ℝ => m₁ {x | n₁ x < r} / l₁ {x | N₁ x < r}) (𝓝[>] 0) (𝓝 c₁) → Tendsto (fun r : ℝ => m₂ {x | n₂ x < r} / l₂ {x | N₂ x < r}) (𝓝[>] 0) (𝓝 c₂) → Tendsto (fun r : ℝ => (m₁.prod m₂) {p | n₁ p.1 + n₂ p.2 < r} / (l₁.prod l₂) {p | N₁ p.1 + N₂ p.2 < r}) (𝓝[>] 0) (𝓝 (c₁ * c₂)) := by
  first | exact @GlobalTheory.SublevelDensity.tendsto_prod_density | exact GlobalTheory.SublevelDensity.tendsto_prod_density | (intros; apply GlobalTheory.SublevelDensity.tendsto_prod_density <;> assumption)
