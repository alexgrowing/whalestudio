import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

noncomputable section

namespace GlobalTheory.ThKLiftConst

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

def lift {n d : ℕ} {X : Spc F E n} {W : Spc F E d} (om : Rep σ X W) (f : UA σ W.J → ℂ)
    (Φ₁ : (Fin n × Fin d → AF F) → ℂ) (μ : Measure (UA σ W.J)) (𝓕 : Set (UA σ W.J)) (g : UA σ X.J) : ℂ :=
  ∫ h in 𝓕, f h * (starRingEnd ℂ) (theta om Φ₁ g h) ∂μ

theorem lift_apply {n d : ℕ} {X : Spc F E n} {W : Spc F E d} (om : Rep σ X W) (f : UA σ W.J → ℂ)
    (Φ₁ : (Fin n × Fin d → AF F) → ℂ) (μ : Measure (UA σ W.J)) (𝓕 : Set (UA σ W.J)) (g : UA σ X.J) :
    lift om f Φ₁ μ 𝓕 g = ∫ h in 𝓕, f h * (starRingEnd ℂ) (theta om Φ₁ g h) ∂μ := rfl

end GlobalTheory.ThKLiftConst
