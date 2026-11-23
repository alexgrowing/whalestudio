import Development.AbelianVarietyTheory.Definitions.Divisors.ZetaActRefl
import Development.AbelianVarietyTheory.Definitions.Divisors.TorsTransport
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.TranslateProduct
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModDefs
open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.LatVal ReciprocityTheory.ChartRestriction.L1 Formalism.L2.Th1.F

namespace GlobalTheory.TauSmul

theorem main : ∀ (γ : SL(2, ℤ)) (τ : ℍ),
    IsTauOf (tauPair (γ • τ)) (UpperHalfPlane.denom γ τ)⁻¹ τ ∧ IsTauOf (tauPair τ) 1 τ := by
  intro γ τ
  have hne : UpperHalfPlane.denom γ τ ≠ 0 := UpperHalfPlane.denom_ne_zero _ τ
  have hd : UpperHalfPlane.denom γ τ = (γ 1 0 : ℂ) * τ + (γ 1 1 : ℂ) := ModularGroup.denom_apply γ τ
  have hs : ((γ • τ : ℍ) : ℂ) = ((γ 0 0 : ℂ) * τ + (γ 0 1 : ℂ)) / ((γ 1 0 : ℂ) * τ + (γ 1 1 : ℂ)) := by
    rw [UpperHalfPlane.coe_specialLinearGroup_apply]; simp
  have hdet : (γ 0 0 : ℂ) * γ 1 1 - γ 0 1 * γ 1 0 = 1 := by
    have h := γ.det_coe
    rw [Matrix.det_fin_two] at h
    exact_mod_cast h
  refine ⟨⟨inv_ne_zero hne, fun x => ?_⟩, one_ne_zero, fun x => ?_⟩
  · rw [PeriodPair.mem_lattice]
    simp only [tauPair]
    rw [hs, hd]
    rw [hd] at hne
    constructor
    · rintro ⟨m, n, rfl⟩
      refine ⟨m * γ 0 0 + n * γ 1 0, m * γ 0 1 + n * γ 1 1, ?_⟩
      push_cast
      rw [eq_inv_mul_iff_mul_eq₀ hne]
      field_simp
      ring
    · rintro ⟨u, v, rfl⟩
      refine ⟨u * γ 1 1 - v * γ 1 0, v * γ 0 0 - u * γ 0 1, ?_⟩
      push_cast
      rw [eq_inv_mul_iff_mul_eq₀ hne]
      field_simp
      linear_combination ((u : ℂ) * τ + v) * hdet
  · rw [PeriodPair.mem_lattice]
    simp only [tauPair, mul_one, one_mul]
    exact ⟨fun ⟨m, n, h⟩ => ⟨m, n, h.symm⟩, fun ⟨m, n, h⟩ => ⟨m, n, h.symm⟩⟩

end GlobalTheory.TauSmul
