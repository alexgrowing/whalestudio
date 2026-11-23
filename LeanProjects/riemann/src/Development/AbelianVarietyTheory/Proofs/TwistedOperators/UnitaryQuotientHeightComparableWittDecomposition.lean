import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.PartFixed
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsVacFOfIsVacVec
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WittAnisotropicGroupNormalizesFlagUnipotent
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnitaryAdelicHeightWittEmbeddingLeConstMulStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsRationalTranslateFlagUnipotentHeightLeStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.UnitaryQuotientHeightWittLeviLePowOfBoundedUnipoStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Asc

namespace GlobalTheory.HtWitt

theorem reduce (hT2 : ∀ (D : D7) (S S₀ : HSp D) (ρ : ℕ) (d : HypDec S S₀ ρ), ∃ C : ℝ, ∀ n ∈ flagN d, ∃ γ ∈ GQ S, γ ∈ flagN d ∧ height S (γ * n) ≤ C) (D : D7) (S S₀ : HSp D) (ρ : ℕ) (d : HypDec S S₀ ρ) :
    ∃ C₁ : ℝ, ∀ n ∈ flagN d, ∀ h : GA D S₀, ∃ n' ∈ flagN d, ∃ h' : GA D S₀, height S n' ≤ C₁ ∧
      height S₀ h' ≤ 2 * quotHeight S₀ h ∧ quotHeight S₀ h' = quotHeight S₀ h ∧
      quotHeight S (n' * d.emb0 h') = quotHeight S (n * d.emb0 h) := by
  obtain ⟨C₁, hC₁⟩ := hT2 D S S₀ ρ d
  refine ⟨C₁, fun n hn h => ?_⟩
  obtain ⟨δ, hδ, hδh⟩ := exists_height_le_two_mul_quotHeight S₀ h
  have hm : d.emb0 δ * n * (d.emb0 δ)⁻¹ ∈ flagN d := GlobalTheory.MixPer.witt_anisotropic_group_normalizes_flag_unipotent D S S₀ ρ d n hn δ
  obtain ⟨γ, hγ, hγN, hγC⟩ := hC₁ _ hm
  refine ⟨γ * (d.emb0 δ * n * (d.emb0 δ)⁻¹), mul_mem hγN hm, δ * h, hγC, hδh, quotHeight_left S₀ hδ h, ?_⟩
  have e : γ * (d.emb0 δ * n * (d.emb0 δ)⁻¹) * d.emb0 (δ * h) = (γ * d.emb0 δ) * (n * d.emb0 h) := by
    rw [map_mul]; group
  rw [e, quotHeight_left S (mul_mem hγ (d.wittDecomp_anisotropicEmbedding_mem_rationalPoints hδ))]

theorem main (hT1 : ∀ (D : D7) (S S₀ : HSp D) (ρ : ℕ) (d : HypDec S S₀ ρ), ∃ C : ℝ, ∀ g : GA D S₀, height S (d.emb0 g) ≤ C * height S₀ g) (hT2 : ∀ (D : D7) (S S₀ : HSp D) (ρ : ℕ) (d : HypDec S S₀ ρ), ∃ C : ℝ, ∀ n ∈ flagN d, ∃ γ ∈ GQ S, γ ∈ flagN d ∧ height S (γ * n) ≤ C) (hT3 : ∀ (D : D7) (S S₀ : HSp D) (ρ : ℕ) (d : HypDec S S₀ ρ) (C₀ : ℝ), ∃ (C : ℝ) (a : ℕ), ∀ n ∈ flagN d, height S n ≤ C₀ → ∀ h : GA D S₀, quotHeight S₀ h ≤ C * quotHeight S (n * d.emb0 h) ^ a) : ∀ (D : D7) (S S₀ : HSp D) (ρ : ℕ) (d : HypDec S S₀ ρ), ∃ (C : ℝ) (a : ℕ), ∀ n ∈ flagN d, ∀ h, quotHeight S₀ h ≤ C * quotHeight S (n * d.emb0 h) ^ a ∧ quotHeight S (n * d.emb0 h) ≤ C * quotHeight S₀ h ^ a := by
  intro D S S₀ ρ d
  obtain ⟨C₁, hC₁⟩ := reduce hT2 D S S₀ ρ d
  obtain ⟨C₂, hC₂⟩ := hT1 D S S₀ ρ d
  obtain ⟨C₃, a₃, hC₃⟩ := hT3 D S S₀ ρ d C₁
  have hC2 : 0 ≤ C₂ := by
    have := hC₂ 1
    rw [map_one, height_one, height_one] at this
    linarith
  refine ⟨max C₃ (C₁ * C₂ * 2) , max a₃ 1, fun n hn h => ?_⟩
  obtain ⟨n', hn', h', hn'C, hh', hq0, hq⟩ := hC₁ n hn h
  have hC1 : 0 ≤ C₁ := (height_pos S n').le.trans hn'C
  have q1 : 1 ≤ quotHeight S (n * d.emb0 h) := one_le_quotHeight S _
  have q0 : 1 ≤ quotHeight S₀ h := one_le_quotHeight S₀ _
  have hM : 0 ≤ max C₃ (C₁ * C₂ * 2) := le_max_of_le_right (by positivity)
  constructor
  · have h3 := hC₃ n' hn' hn'C h'
    rw [hq0, hq] at h3
    exact h3.trans (mul_le_mul (le_max_left _ _) (pow_le_pow_right₀ q1 (le_max_left _ _)) (by positivity) hM)
  · have hb : quotHeight S (n' * d.emb0 h') ≤ C₁ * C₂ * 2 * quotHeight S₀ h := by
      have h1 := height_mul_le S n' (d.emb0 h')
      have h2 := hC₂ h'
      have hp : 0 ≤ height S (d.emb0 h') := (height_pos S _).le
      calc quotHeight S (n' * d.emb0 h') ≤ height S n' * height S (d.emb0 h') := (quotHeight_le_height S _).trans h1
        _ ≤ C₁ * (C₂ * height S₀ h') := mul_le_mul hn'C h2 hp hC1
        _ ≤ C₁ * (C₂ * (2 * quotHeight S₀ h)) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hh' hC2) hC1
        _ = C₁ * C₂ * 2 * quotHeight S₀ h := by ring
    rw [hq] at hb
    refine hb.trans (mul_le_mul (le_max_right _ _) ?_ (by linarith) hM)
    calc quotHeight S₀ h = quotHeight S₀ h ^ 1 := (pow_one _).symm
      _ ≤ _ := pow_le_pow_right₀ q0 (le_max_right _ _)

end GlobalTheory.HtWitt

namespace GlobalTheory.HtWitt

theorem quotHeight_witt : ∀ (D : D7) (S S₀ : HSp D) (ρ : ℕ) (d : HypDec S S₀ ρ), ∃ (C : ℝ) (a : ℕ), ∀ n ∈ flagN d, ∀ h, quotHeight S₀ h ≤ C * quotHeight S (n * d.emb0 h) ^ a ∧ quotHeight S (n * d.emb0 h) ≤ C * quotHeight S₀ h ^ a :=
  main GlobalTheory.T.unitaryAdelicHeight_wittEmbedding_le_const_mul GlobalTheory.T.exists_rational_translate_flagUnipotent_height_le GlobalTheory.T.unitaryQuotientHeight_wittLevi_le_pow_of_boundedUnipotent

end GlobalTheory.HtWitt
