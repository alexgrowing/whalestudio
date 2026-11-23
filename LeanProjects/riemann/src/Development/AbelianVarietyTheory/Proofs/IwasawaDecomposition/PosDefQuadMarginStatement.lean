import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PosDefQuadMargin
import Mathlib
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_margin_quadForm_pos_of_perturbation : ∀ {ι : Type} [Fintype ι] (M : ι → ι → ℝ), (∀ c : ι → ℝ, c ≠ 0 → 0 < ∑ i, ∑ j, c i * c j * M i j) → ∃ η : ℝ, 0 < η ∧ ∀ E : ι → ι → ℝ, (∀ i j, |E i j| ≤ η) → ∀ c : ι → ℝ, c ≠ 0 → 0 < ∑ i, ∑ j, c i * c j * (M i j + E i j) := by
  first | exact @GlobalTheory.posDef_quad_margin | exact GlobalTheory.posDef_quad_margin | (intros; apply GlobalTheory.posDef_quad_margin <;> assumption)
