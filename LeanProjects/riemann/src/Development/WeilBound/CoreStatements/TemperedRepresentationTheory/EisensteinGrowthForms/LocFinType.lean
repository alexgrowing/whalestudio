import Mathlib

noncomputable section

namespace SiegelEisensteinSeries

open Filter Topology

variable {E : Type*} [AddCommGroup E] [Module ℂ E]

def WHolo (D : Set (E →ₗ[ℂ] ℂ)) (f : ℂ → E) (U : Set ℂ) : Prop :=
  ∀ ν ∈ D, DifferentiableOn ℂ (fun s => ν (f s)) U

def Separating (D : Set (E →ₗ[ℂ] ℂ)) : Prop :=
  ∀ v : E, v ≠ 0 → ∃ ν ∈ D, ν v ≠ 0

structure LinSys (E : Type*) [AddCommGroup E] [Module ℂ E] (I : Type*) where
  a : I → ℂ → E →ₗ[ℂ] ℂ
  c : I → ℂ → ℂ

variable {I : Type*}

def LinSys.Sol (Ξ : LinSys E I) (s : ℂ) : Set E := {v | ∀ i, Ξ.a i s v = Ξ.c i s}

def LinSys.FinTypeOn (D : Set (E →ₗ[ℂ] ℂ)) (Ξ : LinSys E I) (W : Set ℂ) : Prop :=
  ∃ (k : ℕ) (Λ : ℂ → Fin k → E), (∀ j, WHolo D (fun s => Λ s j) W) ∧
    (∀ i j, DifferentiableOn ℂ (fun s => Ξ.a i s (Λ s j)) W) ∧
    ∀ s ∈ W, Ξ.Sol s ⊆ Submodule.span ℂ (Set.range (Λ s))

def LinSys.LocFinType (D : Set (E →ₗ[ℂ] ℂ)) (Ξ : LinSys E I) (Ω : Set ℂ) : Prop :=
  ∀ s₀ ∈ Ω, ∃ W : Set ℂ, IsOpen W ∧ s₀ ∈ W ∧ W ⊆ Ω ∧ Ξ.FinTypeOn D W

end SiegelEisensteinSeries
