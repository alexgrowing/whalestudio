import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConvUAbsU

open MeasureTheory GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.SatakeBound GlobalTheory.WeylCell Formalism.UG

noncomputable section

namespace GlobalTheory.UnipShiftU

variable {L : Type} [Field L]

theorem unipB_mul_apply_succ {n : ℕ} {X Y : GL (Fin n) L} (hX : X ∈ unipB L (Fin n)) (hY : Y ∈ unipB L (Fin n))
    {a a' : Fin n} (h : a'.val = a.val + 1) :
    ((X * Y : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) a a' =
      (X : Matrix (Fin n) (Fin n) L) a a' + (Y : Matrix (Fin n) (Fin n) L) a a' := by
  rw [mem_unipB] at hX hY
  have hne : a ≠ a' := fun e => by have := congrArg Fin.val e; omega
  rw [Units.val_mul, Matrix.mul_apply, Finset.sum_eq_add_of_mem a a' (Finset.mem_univ _) (Finset.mem_univ _) hne]
  · rw [hX.2 a, hY.2 a', one_mul, mul_one, add_comm]
  · intro c _ hc
    have h1 := Fin.val_injective.ne hc.1
    have h2 := Fin.val_injective.ne hc.2
    by_cases hca : c < a
    · rw [hX.1 a c hca, zero_mul]
    · have : a' < c := by rw [Fin.lt_iff_val_lt_val] at hca ⊢; omega
      rw [hY.1 c a' this, mul_zero]

theorem unipB_inv_apply_succ {n : ℕ} {X : GL (Fin n) L} (hX : X ∈ unipB L (Fin n))
    {a a' : Fin n} (h : a'.val = a.val + 1) :
    ((X⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) a a' = -(X : Matrix (Fin n) (Fin n) L) a a' := by
  have hne : a ≠ a' := fun e => by have := congrArg Fin.val e; omega
  have e := unipB_mul_apply_succ hX (inv_mem hX) h
  rw [mul_inv_cancel, Units.val_one, Matrix.one_apply_ne hne] at e
  linear_combination -e

theorem conj_apply {n : ℕ} {s : Equiv.Perm (Fin n)} {y : GL (Fin n) L} (hy : IsWeylRep s y)
    (X : Matrix (Fin n) (Fin n) L) (i j : Fin n) :
    (((y⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) * X * (y : Matrix (Fin n) (Fin n) L)) i j =
      ((y⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i (s i) * X (s i) (s j) *
        (y : Matrix (Fin n) (Fin n) L) (s j) j := by
  have hi := hy.inv
  rw [Matrix.mul_apply, Finset.sum_eq_single (s j)]
  · rw [Matrix.mul_apply, Finset.sum_eq_single (s i)]
    · intro b _ hb
      rw [hi i b (by intro e; apply hb; rw [e]; simp), zero_mul]
    · simp
  · intro b _ hb; rw [hy b j hb, mul_zero]
  · simp

theorem inv_mul_diag {n : ℕ} {s : Equiv.Perm (Fin n)} {y : GL (Fin n) L} (hy : IsWeylRep s y) (i : Fin n) :
    ((y⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i (s i) * (y : Matrix (Fin n) (Fin n) L) (s i) i = 1 := by
  have h : ((y⁻¹ * y : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i i = ((1 : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i i := by
    rw [inv_mul_cancel]
  rw [Units.val_mul, Matrix.mul_apply, Finset.sum_eq_single (s i), Units.val_one, Matrix.one_apply_eq] at h
  · exact h
  · intro b _ hb
    rw [hy.inv i b (by intro e; apply hb; rw [e]; simp), zero_mul]
  · simp

theorem swap_inversion {n : ℕ} {a a' p q : Fin n} (h : a'.val = a.val + 1) (hpq : p < q)
    (hs : Equiv.swap a a' q < Equiv.swap a a' p) : p = a ∧ q = a' := by
  rw [Equiv.swap_apply_def, Equiv.swap_apply_def] at hs
  rw [Fin.lt_iff_val_lt_val] at hpq
  split_ifs at hs with h1 h2 h3 h4 h5 h6 <;> simp only [Fin.lt_iff_val_lt_val, Fin.ext_iff] at * <;> omega

theorem transvection_apply' {n : ℕ} (a a' : Fin n) (d : L) (i j : Fin n) :
    Matrix.transvection a a' d i j = (if i = j then 1 else 0) + (if i = a ∧ j = a' then d else 0) := by
  simp only [Matrix.transvection, Matrix.add_apply, Matrix.one_apply, Matrix.single_apply]
  congr 1
  by_cases h1 : a = i <;> by_cases h2 : a' = j <;> simp [h1, h2, eq_comm]

theorem ordL_one [Valued L (WithZero (Multiplicative ℤ))] : ordL (1 : L) = 0 := by
  unfold ordL
  rw [dif_neg (by simp)]
  simp
  rfl

end GlobalTheory.UnipShiftU

namespace GlobalTheory.UnipShiftU

end GlobalTheory.UnipShiftU

namespace GlobalTheory.UnipShiftU

end GlobalTheory.UnipShiftU
