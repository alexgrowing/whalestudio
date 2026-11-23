import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaStabilizerExistsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LeviEmbeddingExistsDoublingConfiguration
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoublingEigenIntertwinerTripleCompatibleStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoublingEigenIntertwinerLocalFactorStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoublingEigenIntertwinerGlobalFactorStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoublingConfigurationLeviIntegralStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoublingConfigurationHaarUnfoldingSecondStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConfigAHaarUnfoldingStatement

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

namespace GlobalTheory.XTermInteg

theorem xTerm_integrableOn : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (b a' : ℕ) (G : Geo σ (b + 2) a') (G₁ : Geo σ b a')
    (H : Plane E (b + 2) b) (H' : Plane E (b + 2 + a') (b + a')), CfgA B G G₁ H H' →
    ∀ e, IsEv B G.M G₁.M H.ι H'.ι (isoA H H') e → ∀ (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W) (om₁ : Rep σ G₁.V G₁.W) (om₁' : Rep σ G₁.V' G₁.W), IsTriple B G X om om' → IsTriple B G₁ X om₁ om₁' →
    ∀ 𝓓 : Set (UA σ G.V.J), IsFundamentalDomain ↥(ratU σ G.V.J ⊓ Subgroup.closure {g : UA σ G.V.J | mat g *ᵥ incV F H.x = incV F H.x}) 𝓓 G.M.μ →
    ∀ Φ ∈ PolData B G.M, ∀ h, IntegrableOn (fun g => thetaSum F (e (G.M.co.rho B.ψ (shiftA H H' 1) (om (g, h) Φ)))) 𝓓 G.M.μ := by
  intro hKP F E _ _ _ _ _ σ B b a' G G₁ H H' hC e he X om om' om₁ om₁' hT hT₁ 𝓓 h𝓓 Φ hΦ h
  obtain ⟨K, μK, μ, hK, -, hμK, hμ⟩ := GlobalTheory.T.theta_stabilizer_exists hKP.base F E σ B (b + 2) G.V _ _ hT.base hT.geo.hV
  obtain ⟨m, hm⟩ := GlobalTheory.LeviElem.levi_exists F E σ B b a' G G₁ H H' hC hT.base hT.geo hT₁.geo
  obtain ⟨μN, c, hμN, hc0, hctop, hI⟩ :=
    GlobalTheory.T.doubling_configuration_haar_unfolding_second F E σ B b a' G G₁ H H' hC hT.base hT.geo hT₁.geo K μK μ hK hμK hμ m hm
  obtain ⟨C, -, hCtop, hU⟩ :=
    GlobalTheory.T.config_a_haar_unfolding F E σ B b a' G G₁ H H' hC hT.base hT.geo hT₁.geo K μK μ hK hμK hμ m hm μN c hμN hc0 hctop hI
  have hf := GlobalTheory.T.doubling_eigen_intertwiner_triple_compatible F E σ B b a' G G₁ H H' hC e he X om om' om₁ om₁' hT hT₁ Φ hΦ h
  have hQ := GlobalTheory.T.doubling_eigen_intertwiner_local_factor hKP F E σ B b a' G G₁ H H' hC e he X om om' om₁ om₁' hT hT₁ Φ hΦ h
  have hN := GlobalTheory.T.doubling_eigen_intertwiner_global_factor hKP F E σ B b a' G G₁ H H' hC e he X om om' om₁ om₁' hT hT₁ Φ hΦ h
  have hfin := GlobalTheory.T.doubling_configuration_levi_integral hKP F E σ B b a' G G₁ H H' hC K μK μ hK hμK hμ m hm e he X om om' om₁ om₁' hT hT₁ Φ hΦ h
  haveI : BorelSpace (UA σ G.V.J) := ⟨rfl⟩
  refine ⟨hf.aestronglyMeasurable, ?_⟩
  have key := hU 𝓓 h𝓓 (fun g => ‖thetaSum F (e (G.M.co.rho B.ψ (shiftA H H' 1) (om (g, h) Φ)))‖ₑ)
    (continuous_enorm.comp hf) (fun q hq g => by simp only [hQ q hq g]) (fun n hn g => by simp only [hN n hn g])
  show ∫⁻ g in 𝓓, ‖thetaSum F (e (G.M.co.rho B.ψ (shiftA H H' 1) (om (g, h) Φ)))‖ₑ ∂G.M.μ < ⊤
  rw [key]
  exact ENNReal.mul_lt_top hCtop.lt_top hfin

end GlobalTheory.XTermInteg
