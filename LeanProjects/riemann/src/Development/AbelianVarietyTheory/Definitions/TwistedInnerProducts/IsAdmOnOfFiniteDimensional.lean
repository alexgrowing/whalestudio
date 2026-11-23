import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms

noncomputable section

open Matrix

namespace GlobalTheory.LinRed

variable {n : ℕ}

structure IsLinRed (G : Set (Matrix (Fin n) (Fin n) ℂ)) : Prop where

  one_mem : (1 : Matrix (Fin n) (Fin n) ℂ) ∈ G

  mul_mem : ∀ g ∈ G, ∀ h ∈ G, g * h ∈ G

  isUnit : ∀ g ∈ G, IsUnit g

  inv_mem : ∀ g ∈ G, g⁻¹ ∈ G

  closed : ∀ g, IsUnit g → g ∈ closure G → g ∈ G

  connected : IsPreconnected G

  star_mem : ∀ g ∈ G, gᴴ ∈ G

def maxCpt (G : Set (Matrix (Fin n) (Fin n) ℂ)) : Set (Matrix (Fin n) (Fin n) ℂ) :=
  G ∩ (Matrix.unitaryGroup (Fin n) ℂ : Set (Matrix (Fin n) (Fin n) ℂ))

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

def IsKStable (G : Set (Matrix (Fin n) (Fin n) ℂ)) (π : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H))
    (S : Submodule ℂ H) : Prop :=
  ∀ k ∈ maxCpt G, ∀ w ∈ S, π k w ∈ S

def IsKFinOn (G : Set (Matrix (Fin n) (Fin n) ℂ)) (π : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (v : H) : Prop :=
  ∃ S : Submodule ℂ H, FiniteDimensional ℂ S ∧ v ∈ S ∧ IsKStable G π S

def IsAdmOn (G : Set (Matrix (Fin n) (Fin n) ℂ)) (π : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) : Prop :=
  Formalism.QuantumDeterminants.IsCRepOn G π ∧ (∀ v, ContinuousOn (fun g => π g v) G) ∧ (∀ k ∈ maxCpt G, ∀ v, ‖π k v‖ = ‖v‖) ∧
    ∀ S : Submodule ℂ H, FiniteDimensional ℂ S → IsKStable G π S →
      (∀ S' : Submodule ℂ H, S' ≤ S → IsKStable G π S' → S' = ⊥ ∨ S' = S) →
      FiniteDimensional ℂ (sSup {S' | ∃ T : H →ₗ[ℂ] H, S' = S.map T ∧
        ∀ k ∈ maxCpt G, ∀ w ∈ S, T (π k w) = π k (T w)} : Submodule ℂ H)

def AnalyticOnGroup (G : Set (Matrix (Fin n) (Fin n) ℂ)) (f : Matrix (Fin n) (Fin n) ℂ → ℂ) : Prop :=
  ∀ g₀ ∈ G, ∃ (U : Set (Fin n → Fin n → ℂ)) (F : (Fin n → Fin n → ℂ) → ℂ),
    IsOpen U ∧ Matrix.of.symm g₀ ∈ U ∧ AnalyticOnNhd ℝ F U ∧ ∀ z ∈ U, Matrix.of z ∈ G → f (Matrix.of z) = F z

end GlobalTheory.LinRed

end
