import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConfigAHaarUnfoldingMeasure
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.config_a_haar_unfolding_measure : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (b a' : ℕ) (G : Geo σ (b + 2) a') (G₁ : Geo σ b a')
    (H : Plane E (b + 2) b) (H' : Plane E (b + 2 + a') (b + a')), CfgA B G G₁ H H' → B.IsGood σ → G.IsGood B → G₁.IsGood B →
    ∀ (K : Subgroup (UA σ G.V.J)) (μK : Measure K) (μ : Measure (AE F E)ˣ), IsStab B K → μK.IsHaarMeasure → μ.IsHaarMeasure →
    ∀ m : (AE F E)ˣ → UA σ G₁.V.J → UA σ G.V.J, (∀ l g₀, IsLevi H l g₀ (m l g₀)) →
    ∀ f : UA σ G.V.J → ℂ, Continuous f →
      ∫⁻ k, ∫⁻ l, ∫⁻ g₀ in G₁.M.dom, ‖f (m l g₀ * k.1)‖ₑ * ENNReal.ofReal ((absE F E l : ℝ) ^ (1 - ((b + 2 : ℕ) : ℝ))) ∂G₁.M.μ ∂μ ∂μK < ⊤ →
      ∫ k, ∫ l, ∫ g₀ in G₁.M.dom, f (m l g₀ * k.1) * (((absE F E l : ℝ) ^ (1 - ((b + 2 : ℕ) : ℝ)) : ℝ) : ℂ) ∂G₁.M.μ ∂μ ∂μK =
        (((∫⁻ k, ∫⁻ l, ∫⁻ g₀ in G₁.M.dom, ENNReal.ofReal ((f (m l g₀ * k.1)).re) * ENNReal.ofReal ((absE F E l : ℝ) ^ (1 - ((b + 2 : ℕ) : ℝ))) ∂G₁.M.μ ∂μ ∂μK).toReal - (∫⁻ k, ∫⁻ l, ∫⁻ g₀ in G₁.M.dom, ENNReal.ofReal (-(f (m l g₀ * k.1)).re) * ENNReal.ofReal ((absE F E l : ℝ) ^ (1 - ((b + 2 : ℕ) : ℝ))) ∂G₁.M.μ ∂μ ∂μK).toReal : ℝ) : ℂ) +
        (((∫⁻ k, ∫⁻ l, ∫⁻ g₀ in G₁.M.dom, ENNReal.ofReal ((f (m l g₀ * k.1)).im) * ENNReal.ofReal ((absE F E l : ℝ) ^ (1 - ((b + 2 : ℕ) : ℝ))) ∂G₁.M.μ ∂μ ∂μK).toReal - (∫⁻ k, ∫⁻ l, ∫⁻ g₀ in G₁.M.dom, ENNReal.ofReal (-(f (m l g₀ * k.1)).im) * ENNReal.ofReal ((absE F E l : ℝ) ^ (1 - ((b + 2 : ℕ) : ℝ))) ∂G₁.M.μ ∂μ ∂μK).toReal : ℝ) : ℂ) * Complex.I := by
  first | exact @GlobalTheory.IterBochner.integral_levi_eq_four | exact GlobalTheory.IterBochner.integral_levi_eq_four | (intros; apply GlobalTheory.IterBochner.integral_levi_eq_four <;> assumption)
