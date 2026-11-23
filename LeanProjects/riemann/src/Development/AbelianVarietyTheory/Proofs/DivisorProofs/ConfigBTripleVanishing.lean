import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SecondConfigurationAuxiliarySpaceStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SecondConfigurationLocalIntertwinerStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SecondConfigurationAuxiliaryModelStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SecondConfigurationGlobalIdentityStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SecondConfigurationNonvanishingStatement

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

namespace GlobalTheory.ConeVLaw

theorem coneTerm_law : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (a b : ℕ) (G : Geo σ a (b + 2)) (G₁ : Geo σ a b) (H : Plane E (b + 2) b) (H' : Plane E (a + (b + 2)) (a + b)), CfgB B G G₁ H H' → ∀ (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W) (om₁ : Rep σ G₁.V G₁.W) (om₁' : Rep σ G₁.V' G₁.W), IsTriple B G X om om' → IsTriple B G₁ X om₁ om₁' → ∀ (V₂ : Spc F E a) (n₁ : ℕ) (X₁ : Spc F E n₁) (H₀ : Plane E a n₁) (j₀ j₁ : ℕ) (M₂ : Model σ X₁ G₁.W) (e₂ : Fn F a (a + (b + 2)) →ₗ[ℂ] Fn F n₁ (a + b)), (reS G.V V₂).IsHerm σ B (a - G.p) G.p → H₀.IsAdapted σ B (reS G.V V₂) X₁ j₀ j₁ → M₂.IsGood B.ψ → IsEv B G.M M₂ H₀.ι H'.ι (isoA H₀ H') e₂ → ∀ γ : {x : Fin a → E // x ≠ 0 ∧ form σ G.V.J x x = 0} → UA σ G.V.J, (∀ x, γ x ∈ ratU σ G.V.J ∧ mat (γ x) *ᵥ incV F x.1 = incV F H₀.x) → ∀ Φ ∈ PolData B G.M, HasLaw G₁.W H' X.α (((b + 2 : ℕ) : ℝ) / 2) (fun h => ∫ g in G.M.dom, ∑' x, thetaSum F (e₂ (G.M.co.rho B.ψ (shiftA H₀ H' 1) (om (γ x * g, h) Φ))) ∂G.M.μ) := by
  intro hKP F E _ _ _ _ _ σ B a b G G₁ H H' hC X om om' om₁ om₁' hT hT₁ V₂ n₁ X₁ H₀ j₀ j₁ M₂ e₂ hV hH₀ hM₂ hE γ hγ Φ hΦ
  obtain ⟨𝓓, h𝓓⟩ := GlobalTheory.T.second_configuration_auxiliary_space F E σ B a b G G₁ H H' hC X om om' om₁ om₁' hT hT₁ V₂ n₁ X₁ H₀ j₀ j₁ M₂ e₂ hV hH₀ hM₂ hE
  intro t m hm h
  obtain ⟨m₀, hm₀⟩ := GlobalTheory.T.second_configuration_auxiliary_model F E σ B a b G G₁ H H' hC X om om' om₁ om₁' hT hT₁ V₂ n₁ X₁ H₀ j₀ j₁ M₂ e₂ hV hH₀ hM₂ hE (Units.map (cA σ : AE F E →* AE F E) t)
  have hU := GlobalTheory.T.second_configuration_local_intertwiner hKP F E σ B a b G G₁ H H' hC X om om' om₁ om₁' hT hT₁ V₂ n₁ X₁ H₀ j₀ j₁ M₂ e₂ hV hH₀ hM₂ hE γ hγ 𝓓 h𝓓 Φ hΦ
  have hI := GlobalTheory.T.second_configuration_global_identity hKP F E σ B a b G G₁ H H' hC X om om' om₁ om₁' hT hT₁ V₂ n₁ X₁ H₀ j₀ j₁ M₂ e₂ hV hH₀ hM₂ hE t m hm m₀ hm₀ Φ hΦ h
  have hMod := GlobalTheory.T.second_configuration_nonvanishing hKP F E σ B a b G G₁ H H' hC X om om' om₁ om₁' hT hT₁ V₂ n₁ X₁ H₀ j₀ j₁ M₂ e₂ hV hH₀ hM₂ hE t m₀ hm₀ 𝓓 h𝓓 Φ hΦ h
  dsimp only
  rw [hU (m * h), hU h, ← hMod]
  simp_rw [hI]
  rw [integral_const_mul]
  ring

end GlobalTheory.ConeVLaw
