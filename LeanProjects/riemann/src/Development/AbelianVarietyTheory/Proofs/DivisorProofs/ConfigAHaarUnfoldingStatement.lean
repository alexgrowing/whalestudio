import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConfigAHaarUnfolding
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.config_a_haar_unfolding : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (b a' : ℕ) (G : Geo σ (b + 2) a') (G₁ : Geo σ b a')
    (H : Plane E (b + 2) b) (H' : Plane E (b + 2 + a') (b + a')), CfgA B G G₁ H H' → B.IsGood σ → G.IsGood B → G₁.IsGood B →
    ∀ (K : Subgroup (UA σ G.V.J)) (μK : Measure K) (μ : Measure (AE F E)ˣ), IsStab B K → μK.IsHaarMeasure → μ.IsHaarMeasure →
    ∀ m : (AE F E)ˣ → UA σ G₁.V.J → UA σ G.V.J, (∀ l g₀, IsLevi H l g₀ (m l g₀)) →
    ∀ (μN : Measure (unip σ G.V H)) (c : ENNReal), μN.IsHaarMeasure → c ≠ 0 → c ≠ ⊤ → (∀ φ : UA σ G.V.J → ENNReal, Measurable φ →
      ∫⁻ g, φ g ∂G.M.μ = c * ∫⁻ k, ∫⁻ l, ∫⁻ g₀, ∫⁻ n, φ (n.1 * m l g₀ * k.1) * ENNReal.ofReal ((absE F E l : ℝ) ^ (1 - ((b + 2 : ℕ) : ℝ))) ∂μN ∂G₁.M.μ ∂μ ∂μK) →
    ∃ C : ENNReal, C ≠ 0 ∧ C ≠ ⊤ ∧ ∀ 𝓓 : Set (UA σ G.V.J), IsFundamentalDomain ↥(ratU σ G.V.J ⊓ Subgroup.closure {g : UA σ G.V.J | mat g *ᵥ incV F H.x = incV F H.x}) 𝓓 G.M.μ →
    ∀ φ : UA σ G.V.J → ENNReal, Continuous φ →
      (∀ q ∈ ratU σ G.V.J ⊓ Subgroup.closure {g : UA σ G.V.J | mat g *ᵥ incV F H.x = incV F H.x}, ∀ g, φ (q * g) = φ g) →
      (∀ n ∈ unip σ G.V H, ∀ g, φ (n * g) = φ g) →
      ∫⁻ g in 𝓓, φ g ∂G.M.μ = C * ∫⁻ k, ∫⁻ l, ∫⁻ g₀ in G₁.M.dom, φ (m l g₀ * k.1) * ENNReal.ofReal ((absE F E l : ℝ) ^ (1 - ((b + 2 : ℕ) : ℝ))) ∂G₁.M.μ ∂μ ∂μK := by
  first | exact @GlobalTheory.UnfoldQ.unfold_stab | exact GlobalTheory.UnfoldQ.unfold_stab | (intros; apply GlobalTheory.UnfoldQ.unfold_stab <;> assumption)
