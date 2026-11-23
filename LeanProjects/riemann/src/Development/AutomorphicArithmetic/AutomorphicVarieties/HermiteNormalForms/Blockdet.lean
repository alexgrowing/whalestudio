import Mathlib

open Matrix
open scoped ComplexOrder

theorem UpperTheory.V.KT.blockdet :
    ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (N : ℕ) (E : Matrix ι ι ℂ) (A : ι → Matrix (Fin N) (Fin N) ℂ),
    (Matrix.of fun s t : Fin N × ι => ∑ φ, star (E φ s.2) * A φ s.1 t.1 * E φ t.2).det =
      (star E.det * E.det) ^ N * ∏ φ, (A φ).det := by
  intro ι _ _ N E A
  have key : (Matrix.of fun s t : Fin N × ι => ∑ φ, star (E φ s.2) * A φ s.1 t.1 * E φ t.2) =
      (Matrix.kronecker (1 : Matrix (Fin N) (Fin N) ℂ) E)ᴴ * Matrix.blockDiagonal A *
        Matrix.kronecker (1 : Matrix (Fin N) (Fin N) ℂ) E := by
    ext ⟨i, a⟩ ⟨j, b⟩
    simp [Matrix.mul_apply, Fintype.sum_prod_type, Matrix.one_apply, Matrix.blockDiagonal_apply,
      Matrix.kronecker, Matrix.kroneckerMap_apply, ite_mul, mul_ite, Finset.sum_ite_eq,
      Finset.sum_ite_eq', Matrix.conjTranspose_apply]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Finset.sum_eq_single i]
    · simp
    · intro k _ hk
      simp [hk]
    · simp
  rw [key, Matrix.det_mul, Matrix.det_mul, Matrix.det_conjTranspose, Matrix.kronecker,
    Matrix.det_kronecker, Matrix.det_blockDiagonal]
  simp [star_pow, mul_pow]
  ring
