import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DatumOfIsIntegersLattice
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.MulStableIntegral
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsDiscreteValuationRingValuationSubringAtPrime
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.AddMonoidHomEqZeroOfEventually

open NumberField IsDedekindDomain WeierstrassCurve GlobalTheory GlobalTheory.Published GlobalTheory.CMModel Formalism.L2.Th1.F
open scoped IntermediateField BigOperators Topology

namespace GlobalTheory.CMModel

theorem mem_of_pow_mem_valSubring (V : ValuationSubring ℂ) {x : ℂ} {n : ℕ} (hn : n ≠ 0) (h : x ^ n ∈ V) :
    x ∈ V := by
  rw [← V.valuation_le_one_iff] at h ⊢
  rw [map_pow] at h
  exact (pow_le_one_iff_of_nonneg zero_le' hn).1 h

theorem inv_two_three_mem (V : ValuationSubring ℂ) (h : V.valuation (6 : ℂ) = 1) :
    (2 : ℂ)⁻¹ ∈ V ∧ (3 : ℂ)⁻¹ ∈ V := by
  have h6 : (6 : ℂ)⁻¹ ∈ V := by
    rw [← V.valuation_le_one_iff, map_inv₀, h, inv_one]
  have h2 : (2 : ℂ) ∈ V := by simpa using natCast_mem V 2
  have h3 : (3 : ℂ) ∈ V := by simpa using natCast_mem V 3
  constructor
  · have : (2 : ℂ)⁻¹ = 3 * 6⁻¹ := by norm_num
    rw [this]; exact mul_mem h3 h6
  · have : (3 : ℂ)⁻¹ = 2 * 6⁻¹ := by norm_num
    rw [this]; exact mul_mem h2 h6

theorem short_coeff_mem (V : ValuationSubring ℂ) (h : V.valuation (6 : ℂ) = 1) (a b j : ℂ) (hj : j ∈ V)
    (hd : -16 * (4 * a ^ 3 + 27 * b ^ 2) ∈ V)
    (he : j * (-16 * (4 * a ^ 3 + 27 * b ^ 2)) = (-48 * a) ^ 3) : a ∈ V ∧ b ∈ V := by
  obtain ⟨h2, h3⟩ := inv_two_three_mem V h
  have h1 : -48 * a ∈ V := mem_of_pow_mem_valSubring V (n := 3) (by norm_num) (he ▸ mul_mem hj hd)
  have ha : a ∈ V := by
    have : a = -(((2 : ℂ)⁻¹) ^ 4 * 3⁻¹ * (-48 * a)) := by ring
    rw [this]
    exact neg_mem (mul_mem (mul_mem (pow_mem h2 4) h3) h1)
  refine ⟨ha, mem_of_pow_mem_valSubring V (n := 2) (by norm_num) ?_⟩
  have h4 : (4 : ℂ) ∈ V := by simpa using natCast_mem V 4
  have : b ^ 2 = ((3 : ℂ)⁻¹) ^ 3 * (-(((2 : ℂ)⁻¹) ^ 4 * (-16 * (4 * a ^ 3 + 27 * b ^ 2))) - 4 * a ^ 3) := by
    ring
  rw [this]
  exact mul_mem (pow_mem h3 3) (sub_mem (neg_mem (mul_mem (pow_mem h2 4) hd)) (mul_mem h4 (pow_mem ha 3)))

theorem modelAt_short_of_six_unit :
    ∀ (V : ValuationSubring ℂ) (F : IntermediateField ℚ ℂ) (a₄ a₆ j u D : ℂ), j ∈ V → j * (⟨0, 0, 0, a₄, a₆⟩ : WeierstrassCurve ℂ).Δ = (⟨0, 0, 0, a₄, a₆⟩ : WeierstrassCurve ℂ).c₄ ^ 3 → V.valuation (6 : ℂ) = 1 → u ∈ F → u ≠ 0 → D ∈ V → V.valuation u ^ 12 * V.valuation D = V.valuation (⟨0, 0, 0, a₄, a₆⟩ : WeierstrassCurve ℂ).Δ → ModelAt V F ⟨0, 0, 0, a₄, a₆⟩ D := by
  intro V F a₄ a₆ j u D hj he h6 hu hu0 hD hv
  set C : VariableChange ℂ := ⟨Units.mk0 u hu0, 0, 0, 0⟩ with hC
  have hΔ : (⟨0, 0, 0, a₄, a₆⟩ : WeierstrassCurve ℂ).Δ = -16 * (4 * a₄ ^ 3 + 27 * a₆ ^ 2) := by
    simp only [WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆,
      WeierstrassCurve.b₈]
    ring
  have hc : (⟨0, 0, 0, a₄, a₆⟩ : WeierstrassCurve ℂ).c₄ = -48 * a₄ := by
    simp only [WeierstrassCurve.c₄, WeierstrassCurve.b₂, WeierstrassCurve.b₄]
    ring
  have hval : V.valuation (u⁻¹ ^ 12 * (⟨0, 0, 0, a₄, a₆⟩ : WeierstrassCurve ℂ).Δ) = V.valuation D := by
    have hvu : V.valuation u ≠ 0 := by simpa using hu0
    rw [map_mul, map_pow, map_inv₀, ← hv, ← mul_assoc, ← mul_pow, inv_mul_cancel₀ hvu, one_pow, one_mul]
  have hmem : u⁻¹ ^ 12 * (⟨0, 0, 0, a₄, a₆⟩ : WeierstrassCurve ℂ).Δ ∈ V := by
    rw [← V.valuation_le_one_iff, hval, V.valuation_le_one_iff]; exact hD
  have hab := short_coeff_mem V h6 (u⁻¹ ^ 4 * a₄) (u⁻¹ ^ 6 * a₆) j hj
    (by convert hmem using 1; rw [hΔ]; ring)
    (by rw [hΔ, hc] at he; linear_combination u⁻¹ ^ 12 * he)
  refine ⟨C, hu, zero_mem F, zero_mem F, zero_mem F, ⟨?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · simp [hC, variableChange_a₁, zero_mem]
  · simp [hC, variableChange_a₂, zero_mem]
  · simp [hC, variableChange_a₃, zero_mem]
  · simpa [hC, variableChange_a₄] using hab.1
  · simpa [hC, variableChange_a₆] using hab.2
  · rw [variableChange_Δ, ← hval]; simp [hC]

end GlobalTheory.CMModel
