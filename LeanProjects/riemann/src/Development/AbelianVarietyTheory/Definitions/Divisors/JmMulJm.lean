import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsAlgLowZero
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.SmoothCartan

noncomputable section

open scoped Matrix.Norms.L2Operator
open ReciprocityTheory.ChartRestriction.DS Matrix

namespace GlobalTheory.Kg

variable {T : Type} [Fintype T] [DecidableEq T] {n : ℕ}

abbrev MatT (T : Type) (n : ℕ) : Type := T → Matrix (Fin n) (Fin n) ℂ

def UJfam (ε : T → Fin n → Bool) : Subgroup (MatT T n)ˣ where
  carrier := {g | ∀ τ, (g.val τ)ᴴ * Jm (ε τ) * g.val τ = Jm (ε τ)}
  one_mem' τ := by simp
  mul_mem' {g h} hg hh τ := by
    simp only [Units.val_mul, Pi.mul_apply, Matrix.conjTranspose_mul]
    calc (h.val τ)ᴴ * (g.val τ)ᴴ * Jm (ε τ) * (g.val τ * h.val τ)
        = (h.val τ)ᴴ * ((g.val τ)ᴴ * Jm (ε τ) * g.val τ) * h.val τ := by simp only [Matrix.mul_assoc]
      _ = Jm (ε τ) := by rw [hg τ, hh τ]
  inv_mem' {g} hg τ := by
    have h1 : g.val τ * (g⁻¹).val τ = 1 := by
      rw [← Pi.mul_apply, ← Units.val_mul, mul_inv_cancel, Units.val_one, Pi.one_apply]
    calc ((g⁻¹).val τ)ᴴ * Jm (ε τ) * (g⁻¹).val τ
        = ((g⁻¹).val τ)ᴴ * ((g.val τ)ᴴ * Jm (ε τ) * g.val τ) * (g⁻¹).val τ := by rw [hg τ]
      _ = (g.val τ * (g⁻¹).val τ)ᴴ * Jm (ε τ) * (g.val τ * (g⁻¹).val τ) := by
          simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = Jm (ε τ) := by rw [h1]; simp

def uJfam (ε : T → Fin n → Bool) : Submodule ℝ (MatT T n) where
  carrier := {X | ∀ τ, (X τ)ᴴ * Jm (ε τ) + Jm (ε τ) * X τ = 0}
  add_mem' {X Y} hX hY τ := by
    simp only [Pi.add_apply, Matrix.conjTranspose_add, Matrix.add_mul, Matrix.mul_add]
    calc (X τ)ᴴ * Jm (ε τ) + (Y τ)ᴴ * Jm (ε τ) + (Jm (ε τ) * X τ + Jm (ε τ) * Y τ)
        = ((X τ)ᴴ * Jm (ε τ) + Jm (ε τ) * X τ) + ((Y τ)ᴴ * Jm (ε τ) + Jm (ε τ) * Y τ) := by abel
      _ = 0 := by rw [hX τ, hY τ, add_zero]
  zero_mem' τ := by simp
  smul_mem' c X hX τ := by
    have h : ((c • X) τ) = (c : ℂ) • X τ := by ext; simp
    rw [h, Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul]
    have hs : star (c : ℂ) = (c : ℂ) := Complex.conj_ofReal c
    rw [hs, ← smul_add]
    simp [hX τ]

def reU (ε : T → Fin n → Bool) (τ : T) (a b : Fin n) : MatT T n :=
  fun σ => if σ = τ then (1 / 2 : ℂ) • (Matrix.single a b 1 - Jm (ε τ) * (Matrix.single a b 1)ᴴ * Jm (ε τ)) else 0

def imU (ε : T → Fin n → Bool) (τ : T) (a b : Fin n) : MatT T n :=
  fun σ => if σ = τ then (-Complex.I / 2) • (Matrix.single a b 1 + Jm (ε τ) * (Matrix.single a b 1)ᴴ * Jm (ε τ)) else 0

end GlobalTheory.Kg

end
