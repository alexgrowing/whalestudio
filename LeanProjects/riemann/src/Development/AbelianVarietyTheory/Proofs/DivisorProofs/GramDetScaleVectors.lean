import Mathlib
import ReciprocityTheory.GeometryOfNumbers.LatticeCovolumes.ConjSymm
open NumberField ReciprocityTheory.GeometryOfNumbersTheory

namespace GlobalTheory

theorem hermFam_form_smul_left {K : Type} [Field K] {V : Type} [AddCommGroup V] [Module K V]
    (h : HermFam K V) (σ : K →+* ℂ) (c : K) (x y : V) :
    h.form σ (c • x) y = starRingEnd ℂ (σ c) * h.form σ x y := by
  rw [← h.conj_symm σ y (c • x), h.smul_right, map_mul, h.conj_symm]

theorem hermFam_gram_det_re_smul {K : Type} [Field K] {V : Type} [AddCommGroup V] [Module K V]
    (h : HermFam K V) (σ : K →+* ℂ) {n : ℕ} (v : Fin n → V) (d : Fin n → K) :
    (h.gram σ (fun j => d j • v j)).det.re = (∏ j, ‖σ (d j)‖ ^ 2) * (h.gram σ v).det.re := by
  have hG : h.gram σ (fun j => d j • v j) =
      Matrix.diagonal (fun j => starRingEnd ℂ (σ (d j))) * h.gram σ v *
        Matrix.diagonal (fun j => σ (d j)) := by
    ext i j
    simp only [HermFam.gram, Matrix.of_apply, Matrix.mul_diagonal, Matrix.diagonal_mul,
      hermFam_form_smul_left, h.smul_right]
    ring
  have hP : (∏ j, starRingEnd ℂ (σ (d j))) * (∏ j, σ (d j)) = ((∏ j, ‖σ (d j)‖ ^ 2 : ℝ) : ℂ) := by
    rw [← Finset.prod_mul_distrib, Complex.ofReal_prod]
    refine Finset.prod_congr rfl fun j _ => ?_
    rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq, Complex.ofReal_pow]
  rw [hG, Matrix.det_mul, Matrix.det_mul, Matrix.det_diagonal, Matrix.det_diagonal,
    mul_right_comm, hP, Complex.re_ofReal_mul]

end GlobalTheory
