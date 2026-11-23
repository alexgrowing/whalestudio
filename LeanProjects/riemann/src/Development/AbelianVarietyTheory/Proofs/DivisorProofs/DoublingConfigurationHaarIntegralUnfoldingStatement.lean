import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoublingConfigurationHaarIntegralUnfolding
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.doubling_configuration_haar_integral_unfolding : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (b a' : ℕ) (G : Geo σ (b + 2) a') (G₁ : Geo σ b a')
    (H : Plane E (b + 2) b) (H' : Plane E (b + 2 + a') (b + a')), CfgA B G G₁ H H' → B.IsGood σ → G.IsGood B → G₁.IsGood B →
    ∀ (K : Subgroup (UA σ G.V.J)) (μK : Measure K) (μ : Measure (AE F E)ˣ), IsStab B K → μK.IsHaarMeasure → μ.IsHaarMeasure →
    ∀ m : (AE F E)ˣ → UA σ G₁.V.J → UA σ G.V.J, (∀ l g₀, IsLevi H l g₀ (m l g₀)) →
    ∃ C : ℂ, C ≠ 0 ∧ ∀ 𝓓 : Set (UA σ G.V.J), IsFundamentalDomain ↥(ratU σ G.V.J ⊓ Subgroup.closure {g : UA σ G.V.J | mat g *ᵥ incV F H.x = incV F H.x}) 𝓓 G.M.μ →
    ∀ f : UA σ G.V.J → ℂ, Continuous f →
      (∀ q ∈ ratU σ G.V.J ⊓ Subgroup.closure {g : UA σ G.V.J | mat g *ᵥ incV F H.x = incV F H.x}, ∀ g, f (q * g) = f g) →
      (∀ n ∈ unip σ G.V H, ∀ g, f (n * g) = f g) →
      ∫⁻ k, ∫⁻ l, ∫⁻ g₀ in G₁.M.dom, ‖f (m l g₀ * k.1)‖ₑ * ENNReal.ofReal ((absE F E l : ℝ) ^ (1 - ((b + 2 : ℕ) : ℝ))) ∂G₁.M.μ ∂μ ∂μK < ⊤ →
      ∫ g in 𝓓, f g ∂G.M.μ = C * ∫ k, ∫ l, ∫ g₀ in G₁.M.dom, f (m l g₀ * k.1) * (((absE F E l : ℝ) ^ (1 - ((b + 2 : ℕ) : ℝ)) : ℝ) : ℂ) ∂G₁.M.μ ∂μ ∂μK := by
  first | exact @GlobalTheory.IwasawaUnfold.iwasawa_unfold | exact GlobalTheory.IwasawaUnfold.iwasawa_unfold | (intros; apply GlobalTheory.IwasawaUnfold.iwasawa_unfold <;> assumption)
