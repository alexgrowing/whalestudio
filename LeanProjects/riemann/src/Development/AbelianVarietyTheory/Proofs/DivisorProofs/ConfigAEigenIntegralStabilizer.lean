import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsotropicVectorTranslationStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNonzeroIsotropicIntegralStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFundamentalDomainClosureStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConfigAEigenThetaTriplesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConfigAEigenIntegralUnimodularStatement

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

namespace GlobalTheory.ThK

theorem unfoldCTBigCone : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (b a' : ℕ) (G : Geo σ (b + 2) a') (G₁ : Geo σ b a')
    (H : Plane E (b + 2) b) (H' : Plane E (b + 2 + a') (b + a')), CfgA B G G₁ H H' →
    ∀ e, IsEv B G.M G₁.M H.ι H'.ι (isoA H H') e → ∀ (K : Subgroup (UA σ G.V.J)) (μK : Measure K) (μ : Measure (AE F E)ˣ), IsStab B K → μK.IsHaarMeasure → μ.IsHaarMeasure →
      ∃ C : ℂ, C ≠ 0 ∧ ∀ X om om' om₁ om₁', IsTriple B G X om om' → IsTriple B G₁ X om₁ om₁' →
      ∀ Φ ∈ PolData B G.M, ∃ A₀ : UA σ G.W.J → ℂ, HasLaw G₁.W H' X.β (((b + 2 : ℕ) : ℝ) / 2) A₀ ∧
        IsCT H' (G.M.I om Φ) (fun h => C * G₁.M.I om₁ (cone B G.M om e K μK μ (shiftA H H') X.ν ((b + 2 - a') / 2) (om (1, h) Φ)) 1 + A₀ h) := by
  intro hKP F E _ _ _ _ _ σ B b a' G G₁ H H' hc e he K μK μ hK hμK hμ
  obtain ⟨C₁, hC₁, hA⟩ := GlobalTheory.T.exists_nonzero_isotropic_integral hKP F E σ B b a' G G₁ H H' hc e he
  obtain ⟨C₂, hC₂, hB2⟩ := GlobalTheory.T.config_a_eigen_integral_unimodular hKP F E σ B b a' G G₁ H H' hc e he K μK μ hK hμK hμ
  refine ⟨C₁ * C₂, mul_ne_zero hC₁ hC₂, ?_⟩
  intro X om om' om₁ om₁' hT hT₁ Φ hΦ
  obtain ⟨γ, hγ⟩ := GlobalTheory.T.exists_isotropic_vector_translation F E σ B b a' G G₁ H H' hc X om om' hT
  obtain ⟨𝓓, h𝓓⟩ := GlobalTheory.T.exists_fundamental_domain_closure F E σ B b a' G G₁ H H' hc X om om' hT
  obtain ⟨A₀, hA₀, hCT⟩ := hA γ hγ X om om' om₁ om₁' hT hT₁ Φ hΦ
  refine ⟨A₀, hA₀, ?_⟩
  have hfun : (fun h => C₁ * ∫ g in G.M.dom, ∑' x, thetaSum F (e (G.M.co.rho B.ψ (shiftA H H' 1) (om (γ x * g, h) Φ))) ∂G.M.μ + A₀ h) =
      (fun h => C₁ * C₂ * G₁.M.I om₁ (cone B G.M om e K μK μ (shiftA H H') X.ν ((b + 2 - a') / 2) (om (1, h) Φ)) 1 + A₀ h) := by
    funext h
    rw [GlobalTheory.T.config_a_eigen_theta_triples hKP F E σ B b a' G G₁ H H' hc e he X om om' om₁ om₁' hT hT₁ γ hγ 𝓓 h𝓓 Φ hΦ h,
      hB2 X om om' om₁ om₁' hT hT₁ 𝓓 h𝓓 Φ hΦ h]
    ring
  rw [← hfun]; exact hCT
end GlobalTheory.ThK
