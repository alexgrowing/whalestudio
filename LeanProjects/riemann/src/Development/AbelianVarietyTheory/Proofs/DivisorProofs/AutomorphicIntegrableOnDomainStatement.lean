import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AutomorphicIntegrableOnDomain
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocFieldLP
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.LiftPair
open scoped Matrix TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.automorphic_integrable_on_domain : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (m : ℕ) (JY : Matrix (Fin m) (Fin m) E), (∀ i j, σ (JY j i) = -JY i j) → JY.det ≠ 0 → ∀ (μ : Measure (UA σ JY)) (𝓕 : Set (UA σ JY)), μ.IsHaarMeasure → IsFundamentalDomain (ratU σ JY) 𝓕 μ → ∀ F₁ : UA σ JY → ℂ, (∀ γ ∈ ratU σ JY, ∀ h, F₁ (γ * h) = F₁ h) → ∀ x : UA σ JY, (IntegrableOn F₁ 𝓕 μ → IntegrableOn (fun h => F₁ (h * x)) 𝓕 μ) ∧ ∫ h in 𝓕, F₁ (h * x) ∂μ = ∫ h in 𝓕, F₁ h ∂μ := by
  first | exact @GlobalTheory.RightTransFD.setIntegral_fd_mul_right | exact GlobalTheory.RightTransFD.setIntegral_fd_mul_right | (intros; apply GlobalTheory.RightTransFD.setIntegral_fd_mul_right <;> assumption)
