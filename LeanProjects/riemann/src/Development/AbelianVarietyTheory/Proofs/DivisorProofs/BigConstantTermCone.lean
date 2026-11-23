import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConfigAEigenIntegralStabilizerStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConfigAEigenIntegralHaarStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnipotentFundamentalDomainStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLeviCharacterModulusStatement

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

namespace GlobalTheory.ThK

theorem ctBigCone (hKP : GlobalTheory.ThK.KP) : GlobalTheory.ThK.CTBigCone := by
  intro F E _ _ _ _ _ σ B b a' G G₁ H H' hc e he K μK μ hK hμK hμ
  obtain ⟨C, hC, hA⟩ := GlobalTheory.T.exists_isCT_integral_eq_cone_integral_add_hasLaw hKP F E σ B b a' G G₁ H H' hc e he K μK μ hK hμK hμ
  refine ⟨C, hC, ?_⟩
  intro X om om' om₁ om₁' hT hT₁ Φ hΦ fa fb hS h₁ m hm h
  obtain ⟨A₀, hA₀, hCT⟩ := hA X om om' om₁ om₁' hT hT₁ Φ hΦ
  obtain ⟨T, hTdef⟩ : ∃ T : UA σ G.W.J → ℂ, T = fun h =>
      C * G₁.M.I om₁ (cone B G.M om e K μK μ (shiftA H H') X.ν ((b + 2 - a') / 2) (om (1, h) Φ)) 1 := ⟨_, rfl⟩
  have hL2 := GlobalTheory.T.config_a_eigen_integral_haar hKP F E σ B b a' G G₁ H H' hc e he K μK μ hK hμK hμ X om om' om₁ om₁' hT hT₁ Φ hΦ

  have hlaw : HasLaw G₁.W H' X.α ((a' : ℝ) / 2) T := by
    intro t m' hm' h'
    rw [hTdef]
    dsimp only
    rw [hL2 t 1 m' hm' h']
    ring

  obtain ⟨ν₀, 𝓕, hH, hF, h1⟩ := GlobalTheory.T.exists_unipotent_fundamental_domain F E σ B b a' G G₁ H H' hc X om om' hT
  obtain ⟨t₀, m₀, hm₀, hne⟩ := GlobalTheory.T.exists_levi_character_modulus F E σ B b a' G G₁ H H' hc X om om' hT
  obtain ⟨hS1, hSa, hSb⟩ := hS
  have hsum : ∀ x, fa x + fb x = T x + A₀ x := by
    intro x
    have e1 := hS1 ν₀ 𝓕 hH hF h1 x
    have e2 := hCT ν₀ 𝓕 hH hF h1 x
    simp only [Pi.add_apply] at e1
    rw [e1, hTdef]; exact e2.symm
  have hfa : ∀ x, fa x = T x := by
    intro x
    have k1 := hSa t₀ m₀ hm₀ x
    have k2 := hlaw t₀ m₀ hm₀ x
    have k3 := hSb t₀ m₀ hm₀ x
    have k4 := hA₀ t₀ m₀ hm₀ x
    have s1 := hsum x
    have s2 := hsum (m₀ * x)
    have : ((X.α t₀ : ℂ) * (((absE F E t₀ : ℝ) ^ ((a' : ℝ) / 2) : ℝ) : ℂ) -
        (X.β t₀ : ℂ) * (((absE F E t₀ : ℝ) ^ (((b + 2 : ℕ) : ℝ) / 2) : ℝ) : ℂ)) * (fa x - T x) = 0 := by
      linear_combination s2 - k1 + k2 - k3 + k4 -
        ((X.β t₀ : ℂ) * (((absE F E t₀ : ℝ) ^ (((b + 2 : ℕ) : ℝ) / 2) : ℝ) : ℂ)) * s1
    rcases mul_eq_zero.mp this with h0 | h0
    · exact absurd (sub_eq_zero.mp h0) hne
    · exact sub_eq_zero.mp h0
  rw [hfa, hTdef]
  dsimp only
  rw [hL2 1 h₁ m hm h]
  simp

end GlobalTheory.ThK
