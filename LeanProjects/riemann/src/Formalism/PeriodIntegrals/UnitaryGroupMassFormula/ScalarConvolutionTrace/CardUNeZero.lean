import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GGMirabolic

open Finset

noncomputable section

open Classical

namespace PI.GGConvScalarW

open Formalism.L2.SG.GGMirabolic

section Defs

variable {F : Type} [Field F] [Fintype F] {k : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]

def projQ (ψ₀ : AddChar F ℂ) (π : Representation ℂ (GL (Fin k) F) V) : V →ₗ[ℂ] V :=
  ((cardU F k : ℂ))⁻¹ • ∑ x : GL (Fin k) F, psiNat ψ₀ x • π x

end Defs

def RepGamConj : Prop :=
  ∀ (F : Type) [Field F] [Fintype F] (k : ℕ) (ψ₀ : AddChar F ℂ) (V : Type) [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GL (Fin k) F) V),
    repGam ψ₀ π = ∑ y : GL (Fin k) F, (π y⁻¹) ∘ₗ projQ ψ₀ π ∘ₗ π y

def RepGamComm : Prop :=
  ∀ (F : Type) [Field F] [Fintype F] (k : ℕ) (ψ₀ : AddChar F ℂ) (V : Type) [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GL (Fin k) F) V) (g : GL (Fin k) F),
    π g ∘ₗ repGam ψ₀ π = repGam ψ₀ π ∘ₗ π g

def QIdem : Prop :=
  ∀ (F : Type) [Field F] [Fintype F] (k : ℕ) (ψ₀ : AddChar F ℂ) (V : Type) [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GL (Fin k) F) V),
    projQ ψ₀ π ∘ₗ projQ ψ₀ π = projQ ψ₀ π

def GenericIff : Prop :=
  ∀ (F : Type) [Field F] [Fintype F] (k : ℕ) (ψ₀ : AddChar F ℂ) (V : Type) [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GL (Fin k) F) V),
    Generic ψ₀ π ↔ projQ ψ₀ π ≠ 0

def RankLeOne : Prop :=
  GelfandGraevMultOne →
  ∀ (F : Type) [Field F] [Fintype F] (k : ℕ) (ψ₀ : AddChar F ℂ), ψ₀ ≠ 1 →
    ∀ (V : Type) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
      (π : Representation ℂ (GL (Fin k) F) V), π.IsIrreducible →
      Module.finrank ℂ (LinearMap.range (projQ ψ₀ π)) ≤ 1

def SchurC : Prop :=
  ∀ (F : Type) [Field F] [Fintype F] (k : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (π : Representation ℂ (GL (Fin k) F) V), π.IsIrreducible →
    ∀ f : V →ₗ[ℂ] V, (∀ g, π g ∘ₗ f = f ∘ₗ π g) → ∃ c : ℂ, f = c • LinearMap.id

def TraceRepGam : Prop :=
  ∀ (F : Type) [Field F] [Fintype F] (k : ℕ) (ψ₀ : AddChar F ℂ) (V : Type) [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] (π : Representation ℂ (GL (Fin k) F) V),
    LinearMap.trace ℂ V (repGam ψ₀ π) =
      (Fintype.card (GL (Fin k) F) : ℂ) * LinearMap.trace ℂ V (projQ ψ₀ π)

def IdemTrace : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] (e : V →ₗ[ℂ] V), e ∘ₗ e = e →
    LinearMap.trace ℂ V e = (Module.finrank ℂ (LinearMap.range e) : ℂ)

def DimPos : Prop :=
  ∀ (F : Type) [Field F] [Fintype F] (k : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (π : Representation ℂ (GL (Fin k) F) V), π.IsIrreducible → 0 < Module.finrank ℂ V

theorem cardU_ne_zero (F : Type) [Field F] [Fintype F] (k : ℕ) : (cardU F k : ℂ) ≠ 0 := by
  rw [Nat.cast_ne_zero]
  unfold cardU
  refine Nat.card_ne_zero.2 ⟨⟨⟨1, ?_⟩⟩, inferInstance⟩
  first
    | (simp [IsUni]; intro i j h; simp [Matrix.one_apply, ne_of_gt h])
    | simp [IsUni]
    | (unfold IsUni; simp)
    | (unfold IsUni; intro i j h; simp [Matrix.one_apply, ne_of_gt h])
    | decide

end PI.GGConvScalarW
