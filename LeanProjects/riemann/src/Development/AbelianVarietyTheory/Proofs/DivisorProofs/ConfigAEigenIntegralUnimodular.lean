import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeviEmbeddingExistsDoublingConfigurationStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoublingConfigurationHaarIntegralUnfoldingStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoublingEigenIntertwinerTripleCompatibleStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoublingEigenIntertwinerLocalFactorStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoublingEigenIntertwinerGlobalFactorStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoublingEigenIntertwinerUnramifiedStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoublingConfigurationLeviIntegralStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoublingConfigurationEigenIntegralStatement

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

namespace GlobalTheory.ThKIwasawa

theorem iwasawaConeTerm : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (b a' : ℕ) (G : Geo σ (b + 2) a') (G₁ : Geo σ b a')
    (H : Plane E (b + 2) b) (H' : Plane E (b + 2 + a') (b + a')), CfgA B G G₁ H H' →
    ∀ e, IsEv B G.M G₁.M H.ι H'.ι (isoA H H') e → ∀ (K : Subgroup (UA σ G.V.J)) (μK : Measure K) (μ : Measure (AE F E)ˣ), IsStab B K → μK.IsHaarMeasure → μ.IsHaarMeasure →
    ∃ C₂ : ℂ, C₂ ≠ 0 ∧ ∀ (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W) (om₁ : Rep σ G₁.V G₁.W) (om₁' : Rep σ G₁.V' G₁.W), IsTriple B G X om om' → IsTriple B G₁ X om₁ om₁' →
    ∀ 𝓓 : Set (UA σ G.V.J), IsFundamentalDomain ↥(ratU σ G.V.J ⊓ Subgroup.closure {g : UA σ G.V.J | mat g *ᵥ incV F H.x = incV F H.x}) 𝓓 G.M.μ →
    ∀ Φ ∈ PolData B G.M, ∀ h,
      ∫ g in 𝓓, thetaSum F (e (G.M.co.rho B.ψ (shiftA H H' 1) (om (g, h) Φ))) ∂G.M.μ = C₂ * G₁.M.I om₁ (cone B G.M om e K μK μ (shiftA H H') X.ν ((b + 2 - a') / 2) (om (1, h) Φ)) 1 := by
  intro hKP F E _ _ _ _ _ σ B b a' G G₁ H H' hC e he K μK μ hK hμK hμ
  classical
  by_cases hg : B.IsGood σ ∧ G.IsGood B ∧ G₁.IsGood B
  swap
  · refine ⟨1, one_ne_zero, ?_⟩
    intro X om om' om₁ om₁' hT hT₁
    exact absurd ⟨hT.base, hT.geo, hT₁.geo⟩ hg
  obtain ⟨m, hm⟩ := GlobalTheory.T.levi_embedding_exists_doubling_configuration F E σ B b a' G G₁ H H' hC hg.1 hg.2.1 hg.2.2
  obtain ⟨C, hC0, hCf⟩ := GlobalTheory.T.doubling_configuration_haar_integral_unfolding F E σ B b a' G G₁ H H' hC hg.1 hg.2.1 hg.2.2 K μK μ hK hμK hμ m hm
  refine ⟨C, hC0, ?_⟩
  intro X om om' om₁ om₁' hT hT₁ 𝓓 h𝓓 Φ hΦ h
  rw [hCf 𝓓 h𝓓 _ (GlobalTheory.T.doubling_eigen_intertwiner_triple_compatible F E σ B b a' G G₁ H H' hC e he X om om' om₁ om₁' hT hT₁ Φ hΦ h)
    (GlobalTheory.T.doubling_eigen_intertwiner_local_factor hKP F E σ B b a' G G₁ H H' hC e he X om om' om₁ om₁' hT hT₁ Φ hΦ h)
    (GlobalTheory.T.doubling_eigen_intertwiner_global_factor hKP F E σ B b a' G G₁ H H' hC e he X om om' om₁ om₁' hT hT₁ Φ hΦ h)
    (GlobalTheory.T.doubling_configuration_levi_integral hKP F E σ B b a' G G₁ H H' hC K μK μ hK hμK hμ m hm e he X om om' om₁ om₁' hT hT₁ Φ hΦ h)]
  congr 1
  rw [← GlobalTheory.T.doubling_configuration_eigen_integral hKP F E σ B b a' G G₁ H H' hC K μK μ hK hμK hμ e he X om om' om₁ om₁' hT hT₁ Φ hΦ h]
  congr 1; funext k; congr 1; funext l; congr 1; funext g₀
  rw [GlobalTheory.T.doubling_eigen_intertwiner_unramified hKP F E σ B b a' G G₁ H H' hC e he X om om' om₁ om₁' hT hT₁ Φ hΦ h l g₀ _ (hm l g₀) k.1]

end GlobalTheory.ThKIwasawa
