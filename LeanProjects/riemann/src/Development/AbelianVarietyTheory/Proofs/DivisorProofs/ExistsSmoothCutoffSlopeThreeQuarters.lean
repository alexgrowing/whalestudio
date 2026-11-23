import Mathlib
import ReciprocityTheory.L2DbarEstimates.Imports
import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.FourSignHolds
import ReciprocityTheory.L2DbarEstimates.LeviForms.Cutoff
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.L2ExtensionLogCanonical
import Development.AbelianVarietyTheory.Definitions.Divisors.EtaleEmpty
open MeasureTheory Filter Topology Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.OTY GlobalTheory.Published.L2Extension
open scoped ENNReal ContDiff

namespace GlobalTheory

theorem exists_isCut (T : ℝ) : ∃ θ : ℝ → ℝ, IsCut T θ := by
  obtain ⟨χ, hχ⟩ : ∃ χ : ℝ → ℝ, ReciprocityTheory.L2DbarEstimates.I.IsCutoff χ :=
    ⟨_, ReciprocityTheory.L2DbarEstimates.I.SmoothCutoff.isCutoff_chi⟩
  obtain ⟨hs, h1, h0, hb, hd⟩ := hχ
  set a : ℝ → ℝ := fun x => (x + T + 1) / 4 + 1 / 2 with ha
  have haS : ContDiff ℝ ∞ a := by
    simp only [ha]; fun_prop
  have hda : ∀ x, HasDerivAt a (1 / 4) x := by
    intro x
    have := (((hasDerivAt_id x).add_const T).add_const 1).div_const 4
    simpa [ha] using this.add_const (1 / 2)
  refine ⟨χ ∘ a, ?_, ?_, ?_, ?_, ?_⟩
  · exact hs.comp haS
  · intro x hx
    exact h1 _ (by simp only [ha]; linarith)
  · intro x hx
    exact h0 _ (by simp only [ha]; linarith)
  · intro x
    exact hb _
  · intro x
    have hχd : DifferentiableAt ℝ χ (a x) :=
      (hs.differentiable (by simp)) _
    have hD : HasDerivAt (χ ∘ a) (deriv χ (a x) * (1 / 4)) x :=
      hχd.hasDerivAt.comp x (hda x)
    rw [hD.deriv, abs_mul]
    have := hd (a x)
    rw [abs_of_pos (by norm_num : (0 : ℝ) < 1 / 4)]
    linarith

theorem exists_isCut₂ : ∀ T : ℝ, ∃ θ : ℝ → ℝ, IsCut T θ := exists_isCut

end GlobalTheory
