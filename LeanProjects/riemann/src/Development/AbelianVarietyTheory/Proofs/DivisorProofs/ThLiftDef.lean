import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

noncomputable section

namespace GlobalTheory.ThK.LiftConst

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

def thLift {n d : ℕ} {X : Spc F E n} {W : Spc F E d} (om : Rep σ X W) (Φ : (Fin n × Fin d → AF F) → ℂ)
    (μ : Measure (UA σ W.J)) (𝓕 : Set (UA σ W.J)) (f : UA σ W.J → ℂ) (g : UA σ X.J) : ℂ :=
  ∫ h in 𝓕, f h * (starRingEnd ℂ) (theta om Φ g h) ∂μ

theorem thLift_def {n d : ℕ} {X : Spc F E n} {W : Spc F E d} (om : Rep σ X W) (Φ : (Fin n × Fin d → AF F) → ℂ)
    (μ : Measure (UA σ W.J)) (𝓕 : Set (UA σ W.J)) (f : UA σ W.J → ℂ) (g : UA σ X.J) :
    thLift om Φ μ 𝓕 f g = ∫ h in 𝓕, f h * (starRingEnd ℂ) (theta om Φ g h) ∂μ := rfl

end GlobalTheory.ThK.LiftConst
