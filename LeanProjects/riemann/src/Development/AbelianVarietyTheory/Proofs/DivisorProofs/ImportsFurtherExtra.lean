import Mathlib

namespace GlobalTheory.SpectralLemmaSecond

open Matrix

theorem main : (let d1 : {m k : Type} → [Fintype m] → [Fintype k] → Matrix m k ℂ → ℝ := @(fun {m k : Type} [Fintype m] [Fintype k] (M : Matrix m k ℂ) ↦ ∑ i : m, ∑ j : k, ‖M i j‖); ∀ {m k p : Type} [inst : Fintype m] [inst_1 : Fintype k] [inst_2 : Fintype p] (M : Matrix m k ℂ) (N : Matrix k p ℂ), d1 (M * N) ≤ d1 M * d1 N) := by
  intro d1 m k p _ _ _ M N
  simp only [d1]
  have hB : ∀ l : k, ∑ j : p, ‖N l j‖ ≤ ∑ l' : k, ∑ j : p, ‖N l' j‖ := fun l =>
    Finset.single_le_sum (f := fun l' => ∑ j : p, ‖N l' j‖)
      (fun _ _ => Finset.sum_nonneg (fun _ _ => norm_nonneg _)) (Finset.mem_univ l)
  calc ∑ i : m, ∑ j : p, ‖(M * N) i j‖
      ≤ ∑ i : m, ∑ j : p, ∑ l : k, ‖M i l‖ * ‖N l j‖ := by
        gcongr with i _ j _
        rw [Matrix.mul_apply]
        refine (norm_sum_le _ _).trans ?_
        gcongr with l _
        exact (norm_mul _ _).le
    _ = ∑ i : m, ∑ l : k, ‖M i l‖ * ∑ j : p, ‖N l j‖ := by
        refine Finset.sum_congr rfl (fun i _ => ?_)
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl (fun l _ => ?_)
        rw [Finset.mul_sum]
    _ ≤ ∑ i : m, ∑ l : k, ‖M i l‖ * ∑ l' : k, ∑ j : p, ‖N l' j‖ := by
        gcongr with i _ l _
        exact hB l
    _ = (∑ i : m, ∑ l : k, ‖M i l‖) * ∑ l' : k, ∑ j : p, ‖N l' j‖ := by
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl (fun i _ => ?_)
        rw [Finset.sum_mul]

end GlobalTheory.SpectralLemmaSecond
