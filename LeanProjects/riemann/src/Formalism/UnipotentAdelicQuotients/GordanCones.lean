import Mathlib

set_option autoImplicit false

namespace GordanCones

def toQ {n : ℕ} (v : Fin n → ℤ) : Fin n → ℚ := fun i => (v i : ℚ)

def cone {n : ℕ} (s : Finset (Fin n → ℤ)) : Set (Fin n → ℚ) :=
  {x | ∃ c : (Fin n → ℤ) → ℚ, (∀ v ∈ s, 0 ≤ c v) ∧ x = ∑ v ∈ s, c v • toQ v}

def dualCone {n : ℕ} (A : Finset (Fin n → ℤ)) : Set (Fin n → ℚ) :=
  {x | ∀ a ∈ A, 0 ≤ ∑ i, (a i : ℚ) * x i}

def Lattice : Prop :=
  ∀ (n : ℕ) (s : Finset (Fin n → ℤ)), ∃ t : Finset (Fin n → ℤ),
    {x : Fin n → ℤ | toQ x ∈ cone s} = {x | ∃ d : (Fin n → ℤ) → ℕ, x = ∑ v ∈ t, d v • v}

def GenIneq : Prop :=
  (∀ (n : ℕ) (A : Finset (Fin n → ℤ)), ∃ s : Finset (Fin n → ℤ), dualCone A = cone s) ∧
  (∀ (n : ℕ) (s : Finset (Fin n → ℤ)), ∃ A : Finset (Fin n → ℤ), cone s = dualCone A)

def Alternative : Prop :=
  ∀ (m n : ℕ) (A : Matrix (Fin m) (Fin n) ℚ) (b : Fin m → ℚ),
    (¬ ∃ x : Fin n → ℚ, ∀ i, ∑ j, A i j * x j < b i) ↔
      ∃ y : Fin m → ℚ, (∀ i, 0 ≤ y i) ∧ y ≠ 0 ∧ (∀ j, ∑ i, y i * A i j = 0) ∧ ∑ i, y i * b i ≤ 0

end GordanCones
