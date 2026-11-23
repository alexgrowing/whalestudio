import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EisAtMinusRho
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocUnifSum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RatStab
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConfigBWittConstantNonzero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolarizedDataIntegralIdentityStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConfigBHaarStabilizerLeftStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConfigBHaarStabilizerRightStatement
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)
open GlobalTheory.ConeSmallUnf

noncomputable section

namespace GlobalTheory.ConeSmallUnf

theorem unfold_series : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (a b : ℕ)
    (G : Geo σ a (b + 2)) (G₁ : Geo σ a b) (H : Plane E (b + 2) b) (H' : Plane E (a + (b + 2)) (a + b)), CfgB B G G₁ H H' →
    ∀ e', IsEv B G.M' G₁.M' H.ι H'.ι (isoB H H') e' → ∀ (K : Subgroup (UA σ G.V'.J)) (μK : Measure K) (μ : Measure (AE F E)ˣ),
    IsStab B K → μK.IsHaarMeasure → μ.IsHaarMeasure →
    ∃ C : ℂ, C ≠ 0 ∧ ∀ X om om' om₁ om₁', IsTriple B G X om om' → IsTriple B G₁ X om₁ om₁' →
    ∀ Φ' ∈ PolData B G.M' ⊓ G.M'.So B.ψ B.τ₁, ∀ Eis : ℂ → UA σ G.V'.J → ℂ, GlobalTheory.ConeSmall.IsEisSer K H.x Eis →
      ∃ s₁ : ℝ, ∀ T : Set (UA σ G.W.J), GlobalTheory.ConeSmallCT.IsReps T H'.x → ∀ s : ℂ, s₁ < s.re →
        GlobalTheory.ConeSmallCT.LocUnifSum (GlobalTheory.ConeSmall.coneI B G G₁ H H' e' K μK μ X.ν om' om₁' Φ' (s + ((a : ℂ) + 1) / 2)) T ∧
        ∀ h, HasSum (fun t : T => C * GlobalTheory.ConeSmall.coneI B G G₁ H H' e' K μK μ X.ν om' om₁' Φ' (s + ((a : ℂ) + 1) / 2) (t.1 * h)) (GlobalTheory.ConeSmallCT.Bint G.M' om' Φ' Eis s h) := by
  intro hKP F E _ _ _ _ _ σ B a b G G₁ H H' hCfg e' he' K μK μ hK hμK hμ
  obtain ⟨C₀, hC₀, ⟨γ, hγ⟩, hCT⟩ := GlobalTheory.T.config_b_witt_constant_nonzero hKP F E σ B a b G G₁ H H' hCfg e' he'
  obtain ⟨c, hc, hR⟩ := GlobalTheory.T.config_B_haar_stabilizer_right hKP F E σ B a b G G₁ H H' hCfg e' he' K μK μ hK hμK hμ
  refine ⟨C₀ * c, mul_ne_zero hC₀ hc, fun X om om' om₁ om₁' hT hT₁ Φ' hΦ' Eis hEis => ?_⟩
  obtain ⟨hf, hI, hdec, -⟩ := id hEis
  obtain ⟨𝓓, h𝓓, s₀, hB⟩ := GlobalTheory.T.polarized_data_integral_identity hKP F E σ B a b G G₁ H H' hCfg K hK X om om' hT Φ' hΦ' hf hI hdec Eis hEis
  obtain ⟨s₁, hcl⟩ := GlobalTheory.T.config_B_haar_stabilizer_left hKP F E σ B a b G G₁ H H' hCfg e' he' K μK μ hK hμK hμ γ hγ X om om' om₁ om₁' hT hT₁
    Φ' hΦ' hf hI hdec 𝓓 h𝓓
  refine ⟨max s₀ s₁, fun T hTr s hs => ?_⟩
  have hs₀ : s₀ < s.re := lt_of_le_of_lt (le_max_left _ _) hs
  have hs₁ : s₁ < s.re := lt_of_le_of_lt (le_max_right _ _) hs
  refine ⟨(hcl s hs₁).2 T hTr, fun h => ?_⟩
  rw [(hB s hs₀ h).1]
  exact hR C₀ γ hγ X om om' om₁ om₁' hT hT₁ Φ' hΦ' (fun h => (hCT γ hγ X om om' om₁ om₁' hT hT₁ Φ' hΦ' h).2) hf hI hdec
    𝓓 h𝓓 s (fun h => (hB s hs₀ h).2) (hcl s hs₁).1 T hTr h

end GlobalTheory.ConeSmallUnf

end
