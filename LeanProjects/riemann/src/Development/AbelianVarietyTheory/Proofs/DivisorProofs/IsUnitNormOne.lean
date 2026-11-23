import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv

noncomputable section

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open scoped TensorProduct

namespace GlobalTheory.PlaneNorm

variable {F E : Type} [Field F] [Field E] [Algebra F E]

def gram2E (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) (x z : Fin M → E) : E :=
  hE σ J x x * hE σ J z z - hE σ J x z * hE σ J z x

def gram2R (R : Type) [CommRing R] [Algebra F R] (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E)
    (a b : Fin M → R ⊗[F] E) : R ⊗[F] E :=
  hR R σ J a a * hR R σ J b b - hR R σ J a b * hR R σ J b a

def IsUnitNorm (R : Type) [CommRing R] [Algebra F R] (σ : E →ₐ[F] E) (a : R ⊗[F] E) : Prop :=
  ∃ s : R ⊗[F] E, IsUnit s ∧ s * sigR R σ s = a

theorem IsUnitNorm.isUnit {R : Type} [CommRing R] [Algebra F R] {σ : E →ₐ[F] E} {a : R ⊗[F] E}
    (h : IsUnitNorm R σ a) : IsUnit a := by
  obtain ⟨s, hs, rfl⟩ := h
  exact hs.mul (hs.map (sigR R σ))

end GlobalTheory.PlaneNorm
