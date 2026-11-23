import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone

noncomputable section

namespace GlobalTheory.ThKCtFin

open scoped TensorProduct NNReal Matrix
open NumberField MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

variable (σ : E →ₐ[F] E) in

def leviElt {d d₁ : ℕ} (W : Spc F E d) (W₁ : Spc F E d₁) (H' : Plane E d d₁) (t : (AE F E)ˣ) : UA σ W.J := by
  classical
  exact if h : ∃ m : UA σ W.J, IsLevi (W₁ := W₁) H' t 1 m then h.choose else 1

theorem isLevi_leviElt {σ : E →ₐ[F] E} {d d₁ : ℕ} {W : Spc F E d} {W₁ : Spc F E d₁} {H' : Plane E d d₁} {t : (AE F E)ˣ}
    (h : ∃ m : UA σ W.J, IsLevi (W₁ := W₁) H' t 1 m) : IsLevi (W₁ := W₁) H' t 1 (leviElt σ W W₁ H' t) := by
  classical
  rw [leviElt, dif_pos h]
  exact h.choose_spec

variable (σ : E →ₐ[F] E) in

def ctLevi {d d₁ : ℕ} (W : Spc F E d) (W₁ : Spc F E d₁) (H' : Plane E d d₁) (μ : Measure (unip σ W H'))
    (𝓕 : Set (unip σ W H')) (f : UA σ W.J → ℂ) (h : UA σ W.J) (t : (AE F E)ˣ) : ℂ :=
  ∫ u in 𝓕, f (u.1 * (leviElt σ W W₁ H' t * h)) ∂μ

theorem ctLevi_apply {σ : E →ₐ[F] E} {d d₁ : ℕ} (W : Spc F E d) (W₁ : Spc F E d₁) (H' : Plane E d d₁)
    (μ : Measure (unip σ W H')) (𝓕 : Set (unip σ W H')) (f : UA σ W.J → ℂ) (h : UA σ W.J) (t : (AE F E)ˣ) :
    ctLevi σ W W₁ H' μ 𝓕 f h t = ∫ u in 𝓕, f (u.1 * (leviElt σ W W₁ H' t * h)) ∂μ := rfl

example {σ : E →ₐ[F] E} {d d₁ : ℕ} (W : Spc F E d) (W₁ : Spc F E d₁) (H' : Plane E d d₁) :
    IsLevi (σ := σ) (W := W) (W₁ := W₁) H' 1 1 (leviElt σ W W₁ H' 1) :=
  isLevi_leviElt ⟨1, by refine ⟨?_, ?_, ?_⟩ <;> simp [mat]⟩

end GlobalTheory.ThKCtFin
