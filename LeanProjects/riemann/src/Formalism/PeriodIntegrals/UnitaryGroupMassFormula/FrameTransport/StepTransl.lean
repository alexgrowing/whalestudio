import Mathlib
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.FrameTransport

noncomputable section

namespace PI.FT

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory
open scoped TensorProduct

section Coe

variable {F E : Type} [Field F] [Field E] [Algebra F E] {R : Type} [CommRing R] [Algebra F R]
  {σ : E →ₐ[F] E} {M : ℕ} {J : Matrix (Fin M) (Fin M) E}

def toHR (g : HA R σ J) : HR R σ J := g

def ofHR (g : HR R σ J) : HA R σ J := g

end Coe

variable (F E : Type) [Field F] [NumberField F] [Field E] [Algebra F E] (σ : E →ₐ[F] E)

def FrameHyp (M : ℕ) (J : Matrix (Fin (M + 1)) (Fin (M + 1)) E) (J' : Matrix (Fin M) (Fin M) E)
    (x : Fin 1 → Fin (M + 1) → E) (β : F) (B : Matrix (Fin (M + 1)) (Fin M) E) : Prop :=
  IsHermND σ J ∧ β ≠ 0 ∧ hE σ J (x 0) (x 0) = algebraMap F E β ∧
    (∀ j, hE σ J (x 0) (fun i => B i j) = 0) ∧
    J' = Formalism.UG.cT (σ : E →+* E) B * J * B ∧ IsHermND σ J'

def StepHomeo : Prop :=
  ∀ (M : ℕ) (J : Matrix (Fin (M + 1)) (Fin (M + 1)) E) (J' : Matrix (Fin M) (Fin M) E)
    (x : Fin 1 → Fin (M + 1) → E) (β : F) (B : Matrix (Fin (M + 1)) (Fin M) E),
    FrameHyp F E σ M J J' x β B →
    ∀ e : Hstab (AF F) σ J x ≃* HA (AF F) σ J',
      (∀ g : Hstab (AF F) σ J x, FrameRel J J' B (g : HA (AF F) σ J) (e g)) →
      Continuous e ∧ Continuous e.symm

def StepRat : Prop :=
  ∀ (M : ℕ) (J : Matrix (Fin (M + 1)) (Fin (M + 1)) E) (J' : Matrix (Fin M) (Fin M) E)
    (x : Fin 1 → Fin (M + 1) → E) (β : F) (B : Matrix (Fin (M + 1)) (Fin M) E),
    FrameHyp F E σ M J J' x β B →
    ∀ e : Hstab (AF F) σ J x ≃* HA (AF F) σ J',
      (∀ g : Hstab (AF F) σ J x, FrameRel J J' B (g : HA (AF F) σ J) (e g)) →
      ∀ g : Hstab (AF F) σ J x,
        g ∈ HstabFin (AF F) σ J x ↔ toHR (e g) ∈ HFinIn (AF F) σ J'

def StepTransl : Prop :=
  ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E) (h : HA (AF F) σ J),
    Continuous (fun g : HA (AF F) σ J => h * g)

end PI.FT
