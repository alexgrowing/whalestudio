import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MatrixMulEntryNormLeUltrametricStatement

namespace GlobalTheory

theorem normalisedPeriod_algebraic_estimate :
    ∀ (E : Type) [NormedField E] [IsUltrametricDist E] (n : Type) [Fintype n] [DecidableEq n]
      (σ : E →+* E) (r M Mi Z : Matrix n n E) (a s t : ℝ), 0 ≤ a → 0 ≤ s → 0 ≤ t →
      (∀ x, ‖σ x‖ = ‖x‖) → M * Mi = 1 → r * M.map σ = M → Z.map σ = Z →
      (∀ i j, ‖M i j‖ ≤ a) → (∀ i j, ‖(Mi - Z) i j‖ ≤ s) → (∀ i j, ‖(r - 1) i j‖ ≤ t) →
      ∀ i j, ‖σ (-(M * Z) i j) - (-(M * Z) i j) - (r - 1) i j‖ ≤ t * (a * s) := by
  intro E _ _ n _ _ σ r M Mi Z a s t ha hs ht hσ hMMi hr hZ hM hD hrt i j
  set D := Mi - Z with hDdef
  set C := M * Z with hCdef
  have hC1 : C = 1 - M * D := by
    rw [hCdef, hDdef, Matrix.mul_sub, hMMi]; abel
  have hCσ : C.map σ = M.map σ * Z := by
    rw [hCdef, Matrix.map_mul, hZ]
  have hrC : r * C.map σ = C := by rw [hCσ, ← Matrix.mul_assoc, hr]
  have hX : C.map σ - 1 = -((M * D).map σ) := by
    rw [hC1, Matrix.map_sub σ (map_sub σ), Matrix.map_one σ (map_zero σ) (map_one σ)]; abel
  have hkey : σ (-C i j) - (-C i j) - (r - 1) i j = ((r - 1) * (C.map σ - 1)) i j := by
    have h2 : ((r - 1) * (C.map σ - 1)) = C - C.map σ - (r - 1) := by
      rw [Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub, hrC, Matrix.one_mul, Matrix.mul_one,
        Matrix.one_mul]; abel
    rw [h2]
    simp [Matrix.sub_apply, Matrix.map_apply, map_neg]
    ring
  have hMD : ∀ i j, ‖(M * D) i j‖ ≤ a * s :=
    GlobalTheory.T.norm_mul_apply_le_of_ultrametric E n M D a s ha hs hM hD
  have hXb : ∀ i j, ‖(C.map σ - 1) i j‖ ≤ a * s := by
    intro i j
    rw [hX, Matrix.neg_apply, norm_neg, Matrix.map_apply, hσ]
    exact hMD i j
  rw [hkey]
  exact GlobalTheory.T.norm_mul_apply_le_of_ultrametric E n (r - 1) (C.map σ - 1) t (a * s) ht (mul_nonneg ha hs) hrt hXb i j

end GlobalTheory
