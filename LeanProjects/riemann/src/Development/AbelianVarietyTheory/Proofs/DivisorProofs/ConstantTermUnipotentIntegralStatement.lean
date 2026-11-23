import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConstantTermUnipotentIntegral
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.constant_term_unipotent_integral : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' → ∀ (d₁ : ℕ) (W₁ : Spc F E d₁) (H' : Plane E (a + a') d₁) (i₀ i₁ : ℕ), H'.IsAdapted σ B G.W W₁ i₀ i₁ → ∀ f : UA σ G.W.J → ℂ, (∀ γ ∈ ratU σ G.W.J, ∀ h, f (γ * h) = f h) → ∀ (μ₀ : Measure (unip σ G.W H')) (𝓕₀ : Set (unip σ G.W H')), μ₀.IsHaarMeasure → IsFundamentalDomain ((ratU σ G.W.J).subgroupOf (unip σ G.W H')) 𝓕₀ μ₀ → μ₀ 𝓕₀ = 1 → IsCT H' f (fun h => ∫ u in 𝓕₀, f (u.1 * h) ∂μ₀) := by
  first | exact @GlobalTheory.UnipCT.isCT_of_fundamentalDomain | exact GlobalTheory.UnipCT.isCT_of_fundamentalDomain | (intros; apply GlobalTheory.UnipCT.isCT_of_fundamentalDomain <;> assumption)
