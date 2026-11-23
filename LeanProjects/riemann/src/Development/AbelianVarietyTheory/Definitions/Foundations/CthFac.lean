import Mathlib

noncomputable section

open scoped UpperHalfPlane MatrixGroups

namespace GlobalTheory.Sieg

def ee (z : ℂ) : ℂ := Complex.exp (2 * Real.pi * Complex.I * z)

def cthFac (c : ℕ) (q t : ℂ) (m : ℕ) : ℂ :=
  (1 - q ^ m * t) ^ (c ^ 2) * (1 - q ^ m * t⁻¹) ^ (c ^ 2) / ((1 - q ^ m * t ^ c) * (1 - q ^ m * (t ^ c)⁻¹))

def cth (c : ℕ) (q t : ℂ) : ℂ :=
  q ^ ((c ^ 2 - 1) / 12) * (-t) ^ (((c : ℤ) - (c : ℤ) ^ 2) / 2) * (1 - t) ^ (c ^ 2) / (1 - t ^ c) *
    ∏' m : ℕ, cthFac c q t (m + 1)

def pt (x : Fin 2 → ℚ) (τ : ℍ) : ℂ := (x 0 : ℂ) * (τ : ℂ) + (x 1 : ℂ)

def sg (c : ℕ) (x : Fin 2 → ℚ) (τ : ℍ) : ℂ := cth c (ee τ) (ee (pt x τ))

open Classical in

def f0 (j : ℕ) (x : Fin 2 → ℚ) : ℂ :=
  if j = 1 then (if Int.fract (x 0) = 0 then (1 / 2) * (1 + ee (x 1)) / (1 - ee (x 1)) else 1 / 2 - ((Int.fract (x 0) : ℚ) : ℂ))
  else -((((Polynomial.bernoulli j).eval (Int.fract (x 0)) : ℚ)) : ℂ) / j

open Classical in

def fTerm (j : ℕ) (x : Fin 2 → ℚ) (τ : ℍ) (p : ℤ × ℤ) : ℂ :=
  if 0 < (x 0 + p.1) * p.2 then
    (Int.sign p.2 : ℂ) * ((x 0 + p.1 : ℚ) : ℂ) ^ (j - 1) * ee (((x 0 + p.1 : ℚ) : ℂ) * p.2 * (τ : ℂ)) * ee ((x 1 : ℂ) * p.2)
  else 0

def F (j : ℕ) (x : Fin 2 → ℚ) (τ : ℍ) : ℂ := f0 j x + ∑' p : ℤ × ℤ, fTerm j x τ p

def cF (c j : ℕ) (x : Fin 2 → ℚ) (τ : ℍ) : ℂ := (c : ℂ) ^ 2 * F j x τ - (c : ℂ) ^ (2 - (j : ℤ)) * F j (c • x) τ

def admitted (c : ℕ) (x : Fin 2 → ℚ) : Prop :=
  1 < c ∧ Nat.Coprime c 6 ∧ ¬ ((c : ℚ) * x 0 ∈ Set.range ((↑) : ℤ → ℚ) ∧ (c : ℚ) * x 1 ∈ Set.range ((↑) : ℤ → ℚ))

end GlobalTheory.Sieg
