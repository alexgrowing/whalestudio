import Mathlib

noncomputable section

namespace GlobalTheory.JacBlock₂

open scoped Matrix

variable {k : Type} [Field k]

def blk {d : ℕ} (i : Fin d) : ℕ := if i.1 = 0 then 0 else if i.1 + 1 = d then 2 else 1

def IsUnipStd {d : ℕ} (u : GL (Fin d) k) : Prop :=
  (∀ i, u.1 i i = 1) ∧ ∀ i j, i ≠ j → ¬ blk i < blk j → u.1 i j = 0

def diagFirst {d : ℕ} (x : kˣ) : GL (Fin d) k where
  val := Matrix.diagonal fun i => if i.1 = 0 then (x : k) else 1
  inv := Matrix.diagonal fun i => if i.1 = 0 then ((x⁻¹ : kˣ) : k) else 1
  val_inv := by
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]; congr 1; funext i; split_ifs <;> simp
  inv_val := by
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]; congr 1; funext i; split_ifs <;> simp

theorem diagFirst_apply {d : ℕ} (x : kˣ) (i j : Fin d) :
    (diagFirst (d := d) x).1 i j = if i = j then (if i.1 = 0 then (x : k) else 1) else 0 := by
  simp [diagFirst, Matrix.diagonal_apply]

end GlobalTheory.JacBlock₂
