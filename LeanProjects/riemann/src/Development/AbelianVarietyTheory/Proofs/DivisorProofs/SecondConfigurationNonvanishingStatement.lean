import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SecondConfigurationNonvanishing
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.second_configuration_nonvanishing : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (a b : ℕ) (G : Geo σ a (b + 2)) (G₁ : Geo σ a b) (H : Plane E (b + 2) b) (H' : Plane E (a + (b + 2)) (a + b)), CfgB B G G₁ H H' → ∀ (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W) (om₁ : Rep σ G₁.V G₁.W) (om₁' : Rep σ G₁.V' G₁.W), IsTriple B G X om om' → IsTriple B G₁ X om₁ om₁' → ∀ (V₂ : Spc F E a) (n₁ : ℕ) (X₁ : Spc F E n₁) (H₀ : Plane E a n₁) (j₀ j₁ : ℕ) (M₂ : Model σ X₁ G₁.W) (e₂ : Fn F a (a + (b + 2)) →ₗ[ℂ] Fn F n₁ (a + b)), (reS G.V V₂).IsHerm σ B (a - G.p) G.p → H₀.IsAdapted σ B (reS G.V V₂) X₁ j₀ j₁ → M₂.IsGood B.ψ → IsEv B G.M M₂ H₀.ι H'.ι (isoA H₀ H') e₂ → ∀ (t : (AE F E)ˣ) (m₀ : UA σ G.V.J), IsLevi (W₁ := X₁) H₀ (Units.map (cA σ : AE F E →* AE F E) t) 1 m₀ → ∀ 𝓓 : Set (UA σ G.V.J), IsFundamentalDomain ↥(ratU σ G.V.J ⊓ Subgroup.closure {g : UA σ G.V.J | mat g *ᵥ incV F H₀.x = incV F H₀.x}) 𝓓 G.M.μ → ∀ Φ ∈ PolData B G.M, ∀ h, (((absE F E t : ℝ) ^ ((a : ℝ) - 1) : ℝ) : ℂ) * ∫ g in 𝓓, thetaSum F (e₂ (G.M.co.rho B.ψ (shiftA H₀ H' 1) (om (m₀⁻¹ * g, h) Φ))) ∂G.M.μ = ∫ g in 𝓓, thetaSum F (e₂ (G.M.co.rho B.ψ (shiftA H₀ H' 1) (om (g, h) Φ))) ∂G.M.μ := by
  first | exact @GlobalTheory.ThK.ConeModulus.integral_translate_levi | exact GlobalTheory.ThK.ConeModulus.integral_translate_levi | (intros; apply GlobalTheory.ThK.ConeModulus.integral_translate_levi <;> assumption)
