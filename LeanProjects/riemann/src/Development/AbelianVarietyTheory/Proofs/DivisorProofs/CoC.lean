import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone

noncomputable section

namespace GlobalTheory.ThK.UnipDom

open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def fA (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) (v w : Fin n → AE F E) : AE F E :=
  v ⬝ᵥ (incM F J *ᵥ fun i => cA σ (w i))

def coA (σ : E →ₐ[F] E) {d d₁ : ℕ} (J : Matrix (Fin d) (Fin d) E) (H' : Plane E d d₁) (g : UA σ J) :
    Fin d₁ → AE F E :=
  fun j => fA σ J (mat g *ᵥ (incM F H'.ι *ᵥ Pi.single j 1)) (incV F H'.y)

def coC (σ : E →ₐ[F] E) {d d₁ : ℕ} (J : Matrix (Fin d) (Fin d) E) (H' : Plane E d d₁) (g : UA σ J) : AE F E :=
  fA σ J (mat g *ᵥ incV F H'.y) (incV F H'.y)

end GlobalTheory.ThK.UnipDom
