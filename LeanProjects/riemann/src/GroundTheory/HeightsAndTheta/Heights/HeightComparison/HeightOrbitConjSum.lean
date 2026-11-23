import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HeightComparison.HeightPtsIntegralPoints
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G

def OrbitConjSum.Statement : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (n : ι → ℕ) (x : Cone n (AlgebraicClosure ℚ))
    (g : (Coord n → ℂ) → ℝ), BlockNonzero x →
    (∀ (c : ι → ℂ) (z : Coord n → ℂ), (∀ k, c k ≠ 0) →
      z ∈ Geo.mcPts (ι := blockIdx n) (orbitIdeal x) → g (fun p ↦ c p.1 * z p) = g z) →
    (Geo.degC (ι := blockIdx n) (orbitIdeal x) : ℝ) *
        ∑ σ : coordField x →+* ℂ, g (fun p ↦ σ (coordVec x p.1 p.2)) =
      (Module.finrank ℚ (coordField x) : ℝ) *
        ∑ᶠ q : projPts (ι := blockIdx n) (orbitIdeal x),
          g (Quot.out q : Geo.mcPts (ι := blockIdx n) (orbitIdeal x))

example : BlockNonzero samplePoint ∧
    ∀ (c : Unit → ℂ) (z : Coord (fun _ : Unit ↦ 1) → ℂ), (∀ k, c k ≠ 0) →
      z ∈ Geo.mcPts (ι := blockIdx (fun _ : Unit ↦ 1)) (orbitIdeal samplePoint) →
      (fun w : Coord (fun _ : Unit ↦ 1) → ℂ ↦ ‖w ⟨(), 0⟩‖ / ‖w ⟨(), 1⟩‖) (fun p ↦ c p.1 * z p) =
        (fun w : Coord (fun _ : Unit ↦ 1) → ℂ ↦ ‖w ⟨(), 0⟩‖ / ‖w ⟨(), 1⟩‖) z := by
  refine ⟨samplePoint_blockNonzero, fun c z hc _ ↦ ?_⟩
  simp only [norm_mul]
  exact mul_div_mul_left _ _ (norm_ne_zero_iff.mpr (hc ()))

end GroundTheory.Heights₂.Heights
