import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.MemMspan

noncomputable section

namespace GlobalTheory.JSW

def colGL {R : Type} [CommRing R] {a : ℕ} (r : ℕ) (x : Fin a → R) : GL (Fin a) R :=
  ⟨1 + Matrix.of (fun i j : Fin a => if (j : ℕ) = r ∧ (i : ℕ) < r then x i else 0),
   1 - Matrix.of (fun i j : Fin a => if (j : ℕ) = r ∧ (i : ℕ) < r then x i else 0),
   by
    have h : Matrix.of (fun i j : Fin a => if (j : ℕ) = r ∧ (i : ℕ) < r then x i else 0) *
        Matrix.of (fun i j : Fin a => if (j : ℕ) = r ∧ (i : ℕ) < r then x i else 0) = 0 := by
      refine Matrix.ext fun i j => ?_
      simp only [Matrix.mul_apply, Matrix.of_apply, Matrix.zero_apply]
      refine Finset.sum_eq_zero fun k _ => ?_
      by_cases hk : (k : ℕ) = r
      · simp [hk]
      · simp [hk]
    rw [mul_sub, add_mul, add_mul, one_mul, mul_one, one_mul, h]; abel,
   by
    have h : Matrix.of (fun i j : Fin a => if (j : ℕ) = r ∧ (i : ℕ) < r then x i else 0) *
        Matrix.of (fun i j : Fin a => if (j : ℕ) = r ∧ (i : ℕ) < r then x i else 0) = 0 := by
      refine Matrix.ext fun i j => ?_
      simp only [Matrix.mul_apply, Matrix.of_apply, Matrix.zero_apply]
      refine Finset.sum_eq_zero fun k _ => ?_
      by_cases hk : (k : ℕ) = r
      · simp [hk]
      · simp [hk]
    rw [sub_mul, mul_add, mul_add, one_mul, mul_one, one_mul, h]; abel⟩

def mirSet (R : Type) [CommRing R] (m : ℕ) : Set (GL (Fin (m + 1)) R) :=
  {g | ∀ j, (g : Matrix (Fin (m + 1)) (Fin (m + 1)) R) (Fin.last m) j = if j = Fin.last m then 1 else 0}

open Classical in

def onMat {n : ℕ} (W : GL (Fin n) ℂ → ℂ) (x : Matrix (Fin n) (Fin n) ℂ) : ℂ :=
  if h : IsUnit x then W h.unit else 0

end GlobalTheory.JSW
