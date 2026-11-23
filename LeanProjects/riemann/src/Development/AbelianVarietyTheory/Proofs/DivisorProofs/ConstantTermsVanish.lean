import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SplitFunctionsAdaptedPlaneStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConfigBEigenThetaTorusStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConfigBConstantTermThetaLiftStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConfigBExistsNonzeroConstantStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConfigBExistsNonzeroCoefficientStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConfigAEigenThetaTorusStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConfigAConstantTermThetaLiftStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConfigAExistsNonzeroConstantStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConfigAExistsNonzeroCoefficientStatement

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

namespace GlobalTheory.ThKCtZero

theorem ctBigZero (kp : GlobalTheory.ThK.KP) : GlobalTheory.ThK.CTBigZero := by
  intro F E _ _ _ _ _ σ B a b G G₁ H H' hc e he
  obtain ⟨κ, hκ, hκ'⟩ := GlobalTheory.T.config_b_exists_nonzero_constant kp F E σ B a b G G₁ H H' hc e he
  obtain ⟨C₀, hC₀, hC₀'⟩ := GlobalTheory.T.config_b_exists_nonzero_coefficient kp F E σ B a b G G₁ H H' hc e he
  refine ⟨C₀ * κ, mul_ne_zero hC₀ hκ, ?_⟩
  intro X om om' om₁ om₁' hT hT₁ Φ hΦ fa fb hs h₁ m hm h
  obtain ⟨c, A₁, hcg, hA₁, hint⟩ := hC₀' X om om' om₁ om₁' hT hT₁ Φ hΦ
  have hct := GlobalTheory.T.config_b_constant_term_theta_lift kp F E σ B a b G G₁ H H' hc X om om' hT Φ hΦ c hcg
  have hval : (fun h => ∫ g in G.M.dom, c g h ∂G.M.μ) =
      A₁ + fun h => C₀ * κ * G₁.M.I om₁ (e (om (1, h) Φ)) 1 := by
    funext h
    obtain ⟨hi, hA⟩ := hint h
    obtain ⟨hi', hv⟩ := hκ' X om om' om₁ om₁' hT hT₁ Φ hΦ h
    have hsplit : (fun g => c g h) = fun g => (c g h - C₀ * thetaSum F (e (om (g, h) Φ))) +
        C₀ * thetaSum F (e (om (g, h) Φ)) := by funext g; ring
    rw [hsplit, integral_add hi (hi'.const_mul C₀), integral_const_mul, hA, hv]
    simp only [Pi.add_apply]; ring
  rw [hval] at hct
  have hlaw : HasLaw G₁.W H' X.β ((a : ℝ) / 2) fun h => C₀ * κ * G₁.M.I om₁ (e (om (1, h) Φ)) 1 := by
    intro t m' hm' h'
    simp only
    rw [GlobalTheory.T.config_b_eigen_theta_torus kp F E σ B a b G G₁ H H' hc e he X om om' om₁ om₁' hT hT₁ Φ hΦ t 1 m' hm' h']
    ring
  have hs' : Split2 G₁.W H' X (G.M.I om Φ) A₁ fun h => C₀ * κ * G₁.M.I om₁ (e (om (1, h) Φ)) 1 := ⟨hct, hA₁, hlaw⟩
  obtain ⟨-, hfb⟩ := GlobalTheory.T.split_functions_adapted_plane kp F E σ B a (b + 2) G.W (a + b) G₁.W H' a (a + b + 1) _ _ _ _ X hT.base hT.geo.lt
    hT.geo.hW hT₁.geo.hW hc.hH' (G.M.I om Φ) fa fb A₁ _ hs hs'
  rw [hfb]
  simp only
  rw [GlobalTheory.T.config_b_eigen_theta_torus kp F E σ B a b G G₁ H H' hc e he X om om' om₁ om₁' hT hT₁ Φ hΦ 1 h₁ m hm h]
  simp

theorem ctSmallZero (kp : GlobalTheory.ThK.KP) : GlobalTheory.ThK.CTSmallZero := by
  intro F E _ _ _ _ _ σ B b a' G G₁ H H' hc e' he'
  obtain ⟨κ, hκ, hκ'⟩ := GlobalTheory.T.config_a_exists_nonzero_constant kp F E σ B b a' G G₁ H H' hc e' he'
  obtain ⟨C₀, hC₀, hC₀'⟩ := GlobalTheory.T.config_a_exists_nonzero_coefficient kp F E σ B b a' G G₁ H H' hc e' he'
  refine ⟨C₀ * κ, mul_ne_zero hC₀ hκ, ?_⟩
  intro X om om' om₁ om₁' hT hT₁ Φ' hΦ'
  refine ⟨fun h => C₀ * κ * G₁.M'.I om₁' (e' (om' (1, h) Φ')) 1, ⟨?_, ?_, ?_⟩, ?_⟩
  · have hct := GlobalTheory.T.config_a_constant_term_theta_lift kp F E σ B b a' G G₁ H H' hc X om om' hT Φ' hΦ' _
      (hC₀' X om om' om₁ om₁' hT hT₁ Φ' hΦ')
    have hval : (fun h => ∫ g in G.M'.dom, C₀ * thetaSum F (e' (om' (g, h) Φ')) ∂G.M'.μ) =
        (fun h => C₀ * κ * G₁.M'.I om₁' (e' (om' (1, h) Φ')) 1) + 0 := by
      funext h
      rw [integral_const_mul, hκ' X om om' om₁ om₁' hT hT₁ Φ' hΦ' h]
      simp only [Pi.add_apply, Pi.zero_apply, add_zero]; ring
    rwa [hval] at hct
  · intro t m hm h
    simp only
    rw [GlobalTheory.T.config_a_eigen_theta_torus kp F E σ B b a' G G₁ H H' hc e' he' X om om' om₁ om₁' hT hT₁ Φ' hΦ' t 1 m hm h]
    ring
  · intro t m hm h
    simp
  · intro h₁ m hm h
    simp only
    rw [GlobalTheory.T.config_a_eigen_theta_torus kp F E σ B b a' G G₁ H H' hc e' he' X om om' om₁ om₁' hT hT₁ Φ' hΦ' 1 h₁ m hm h]
    simp

theorem ctZero : GlobalTheory.ThK.KP → GlobalTheory.ThK.CTBigZero ∧ GlobalTheory.ThK.CTSmallZero := fun kp => ⟨ctBigZero kp, ctSmallZero kp⟩

end GlobalTheory.ThKCtZero
