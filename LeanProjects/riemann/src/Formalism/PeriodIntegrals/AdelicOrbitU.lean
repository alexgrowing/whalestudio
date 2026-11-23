import Mathlib
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes

noncomputable section

namespace PI.AdelicOrbitU

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Matrix
open scoped TensorProduct

section Vol

variable (F E : Type) [Field F] [NumberField F] [Field E] [Algebra F E] (σ : E →ₐ[F] E)

def AdelicOrbit : Prop :=
  ∀ (M : ℕ) (J : Matrix (Fin (M + 1)) (Fin (M + 1)) E) (x : Fin 1 → Fin (M + 1) → E) (β : F),
    IsHermND σ J → β ≠ 0 → hE σ J (x 0) (x 0) = algebraMap F E β →
    ∀ y : Fin 1 → Fin (M + 1) → AF F ⊗[F] E, qR (AF F) σ J (y 0) = algebraMap F (AF F) β →
      ∃ g : HA (AF F) σ J, g • ratTup (AF F) x = y

end Vol

def AdelicOrbitQuad : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E),
    Module.finrank F E = 2 → (∀ a : E, σ a = a ↔ a ∈ (algebraMap F E).range) → AdelicOrbit F E σ

end PI.AdelicOrbitU
