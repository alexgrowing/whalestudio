import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TripleRestrictionHermitianAdaptedPlane
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.triple_restriction_hermitian_adapted_plane : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (a b : ℕ) (G : Geo σ a (b + 2)) (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' → ∀ (V₂ : Spc F E a) (n₁ : ℕ) (X₁ : Spc F E n₁) (H₀ : Plane E a n₁) (j₀ j₁ d₂ : ℕ) (W₂ : Spc F E d₂) (M₂ : Model σ X₁ W₂), (reS G.V V₂).IsHerm σ B (a - G.p) G.p → H₀.IsAdapted σ B (reS G.V V₂) X₁ j₀ j₁ → M₂.IsGood B.ψ → ∀ (t : (AE F E)ˣ) (m₀ : UA σ G.V.J), IsLevi (W₁ := X₁) H₀ (Units.map (cA σ : AE F E →* AE F E) t) 1 m₀ → ∀ 𝓓 : Set (UA σ G.V.J), IsFundamentalDomain ↥(ratU σ G.V.J ⊓ Subgroup.closure {g : UA σ G.V.J | mat g *ᵥ incV F H₀.x = incV F H₀.x}) 𝓓 G.M.μ → ∀ φ : UA σ G.V.J → ENNReal, AEMeasurable φ G.M.μ → (∀ q ∈ ratU σ G.V.J ⊓ Subgroup.closure {g : UA σ G.V.J | mat g *ᵥ incV F H₀.x = incV F H₀.x}, ∀ g, φ (q * g) = φ g) → (∀ n ∈ unip σ G.V H₀, ∀ g, φ (n * g) = φ g) → ENNReal.ofReal ((absE F E t : ℝ) ^ ((a : ℝ) - 1)) * ∫⁻ g in 𝓓, φ (m₀⁻¹ * g) ∂G.M.μ = ∫⁻ g in 𝓓, φ g ∂G.M.μ := by
  first | exact @GlobalTheory.ThK.LeviModulus.integral_levi_translate | exact GlobalTheory.ThK.LeviModulus.integral_levi_translate | (intros; apply GlobalTheory.ThK.LeviModulus.integral_levi_translate <;> assumption)
