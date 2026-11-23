import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.DatumOfIsIntegersLattice
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.MulStableIntegral
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsDiscreteValuationRingValuationSubringAtPrime
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.AddMonoidHomEqZeroOfEventually

open WeierstrassCurve

namespace GlobalTheory.CMModel

theorem exists_intV_variableChange (W : WeierstrassCurve ℂ) [W.IsElliptic] (V : ValuationSubring ℂ)
    (u : ℂˣ) (hj : W.j ∈ V) (hu : V.valuation (u : ℂ) ^ 12 = V.valuation W.Δ) :
    ∃ r s t : ℂ, IntV V ((⟨u, r, s, t⟩ : VariableChange ℂ) • W) := by
  have : IsIntegrallyClosedIn V ℂ := (isIntegrallyClosed_iff_isIntegrallyClosedIn ℂ).1 inferInstance
  have ht : HasRationalTorsion W ℂ 12 := by
    intro x y h hn
    exact ⟨⟨x, rfl⟩, ⟨y, rfl⟩⟩
  obtain ⟨C, W₀, e, h₀⟩ := exists_integral_model V (L := ℂ) (W := W) ⟨⟨W.j, hj⟩, rfl⟩ ht
  have hΔ : ((C.u⁻¹ : ℂˣ) : ℂ) ^ 12 * W.Δ = 1 := by
    rw [← variableChange_Δ, e, WeierstrassCurve.baseChange, map_Δ, h₀, map_one]
  have hCu : (C.u : ℂ) ≠ 0 := C.u.ne_zero
  have hu0 : (u : ℂ) ≠ 0 := u.ne_zero
  have hΔ' : W.Δ = (C.u : ℂ) ^ 12 := by
    rw [Units.val_inv_eq_inv_val] at hΔ
    field_simp at hΔ
    exact hΔ
  have hv : V.valuation (u : ℂ) = V.valuation (C.u : ℂ) := by
    rw [hΔ', map_pow] at hu
    exact (pow_left_inj₀ zero_le' zero_le' (by norm_num)).1 hu
  have hw : (C.u : ℂ) / u ∈ V := by
    rw [← V.valuation_le_one_iff, map_div₀, hv, div_self]
    exact (map_ne_zero _).2 hCu
  have h1 : (C • W).a₁ ∈ V := by rw [e]; exact W₀.a₁.2
  have h2 : (C • W).a₂ ∈ V := by rw [e]; exact W₀.a₂.2
  have h3 : (C • W).a₃ ∈ V := by rw [e]; exact W₀.a₃.2
  have h4 : (C • W).a₄ ∈ V := by rw [e]; exact W₀.a₄.2
  have h6 : (C • W).a₆ ∈ V := by rw [e]; exact W₀.a₆.2
  refine ⟨C.r, C.s, C.t, ?_, ?_, ?_, ?_, ?_⟩
  · convert V.mul_mem _ _ hw h1 using 1
    simp only [variableChange_a₁, Units.val_inv_eq_inv_val]; field_simp
  · convert V.mul_mem _ _ (pow_mem hw 2) h2 using 1
    simp only [variableChange_a₂, Units.val_inv_eq_inv_val]; field_simp
  · convert V.mul_mem _ _ (pow_mem hw 3) h3 using 1
    simp only [variableChange_a₃, Units.val_inv_eq_inv_val]; field_simp
  · convert V.mul_mem _ _ (pow_mem hw 4) h4 using 1
    simp only [variableChange_a₄, Units.val_inv_eq_inv_val]; field_simp
  · convert V.mul_mem _ _ (pow_mem hw 6) h6 using 1
    simp only [variableChange_a₆, Units.val_inv_eq_inv_val]; field_simp

end GlobalTheory.CMModel
