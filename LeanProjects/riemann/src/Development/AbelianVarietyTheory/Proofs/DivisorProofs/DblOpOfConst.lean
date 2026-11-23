import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone

noncomputable section

namespace GlobalTheory.ThK.DoublingLifts

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
  {n d : ℕ} {X : Spc F E n} {W : Spc F E d}

def liftW (om : Rep σ X W) (μ : Measure (UA σ W.J)) (𝓕 : Set (UA σ W.J)) (Φ₂ : (Fin n × Fin d → AF F) → ℂ)
    (f : UA σ W.J → ℂ) (g : UA σ X.J) : ℂ :=
  ∫ h in 𝓕, f h * starRingEnd ℂ (theta om Φ₂ g h) ∂μ

def dblOp (M : Model σ X W) (om : Rep σ X W) (μ : Measure (UA σ W.J)) (𝓕 : Set (UA σ W.J))
    (Φ₁ Φ₂ : (Fin n × Fin d → AF F) → ℂ) (f : UA σ W.J → ℂ) : UA σ W.J → ℂ :=
  fun h => ∫ g in M.dom, theta om Φ₁ g h * liftW om μ 𝓕 Φ₂ f g ∂M.μ

end GlobalTheory.ThK.DoublingLifts

end
