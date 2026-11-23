import Formalism.LocalToGlobal.PairingIndexBounds.ModelLatticeMoves.IsBichar
import Formalism.LocalToGlobal.TorsionIntegrality.QuadraticSemicharacters.IsSemiChar

noncomputable section
open scoped BigOperators

namespace Formalism.L2.PairingIndexBounds.Mv

open Formalism.L2.Th1.H

variable {V : Type*} [AddCommGroup V] [Module ℂ V]

def wU (H : Sesq V) (α : V → ℂ) (x : V) : (V → ℂ) →ₗ[ℂ] (V → ℂ) where
  toFun F z := α x * opU H x F z
  map_add' F G := by funext z; simp [opU, mul_add, add_mul]
  map_smul' r F := by funext z; simp [opU, smul_eq_mul]; ring

def cU (H : Sesq V) (A B : AddSubgroup V) (b : B) (a : A) : ℂ :=
  Complex.exp (-(2 * (Real.pi : ℂ)) * Complex.I * (altE H (a : V) (b : V) : ℂ))

def wA (H : Sesq V) (α : V → ℂ) (A : AddSubgroup V) (a : A) : (V → ℂ) →ₗ[ℂ] (V → ℂ) := wU H α (a : V)

def wB (H : Sesq V) (α : V → ℂ) (B : AddSubgroup V) (b : B) : (V → ℂ) →ₗ[ℂ] (V → ℂ) := wU H α (b : V)

def GoodLat (H : Sesq V) (α : V → ℂ) (A B Λ : AddSubgroup V) : Prop :=
  IsSemiChar H Λ α ∧ Λ ≤ (Λ ⊓ A) ⊔ (Λ ⊓ B) ∧
    (∀ a ∈ A, ∀ b ∈ B, a + b ∈ Λ → a ∈ Λ) ∧
    (∀ a ∈ A, (∀ b ∈ B, b ∈ Λ → ∃ m : ℤ, altE H a b = m) → a ∈ Λ) ∧
    (∀ b ∈ B, (∀ a ∈ A, a ∈ Λ → ∃ m : ℤ, altE H a b = m) → b ∈ Λ)

def volA (A Λ₀ Λ : AddSubgroup V) : ℝ :=
  (((Λ₀ ⊓ A).relIndex (Λ ⊓ A) : ℕ) : ℝ) / (((Λ ⊓ A).relIndex (Λ₀ ⊓ A) : ℕ) : ℝ)

end Formalism.L2.PairingIndexBounds.Mv
