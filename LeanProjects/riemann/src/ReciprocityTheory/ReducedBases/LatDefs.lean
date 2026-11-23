import Mathlib

noncomputable section

namespace ReciprocityTheory.ReducedBases

open Matrix

def toReal {d : ℕ} (x : Fin d → ℤ) : Fin d → ℝ := fun i => (x i : ℝ)

def polar {d : ℕ} (A : Matrix (Fin d) (Fin d) ℝ) (x y : Fin d → ℤ) : ℝ :=
  toReal x ⬝ᵥ (A *ᵥ toReal y)

def Q {d : ℕ} (A : Matrix (Fin d) (Fin d) ℝ) (x : Fin d → ℤ) : ℝ := polar A x x / 2

def SameClass {d : ℕ} (N : ℤ) (a b : Fin d → ℤ) : Prop := ∃ w : Fin d → ℤ, a = b + N • w

def IsMinInClass {d : ℕ} (F : (Fin d → ℤ) → ℝ) (N : ℤ) (a : Fin d → ℤ) : Prop :=
  ∀ w : Fin d → ℤ, F a ≤ F (a + N • w)

def IsUniqueMinInClass {d : ℕ} (F : (Fin d → ℤ) → ℝ) (N : ℤ) (a : Fin d → ℤ) : Prop :=
  ∀ w : Fin d → ℤ, w ≠ 0 → F a < F (a + N • w)

end ReciprocityTheory.ReducedBases

end
