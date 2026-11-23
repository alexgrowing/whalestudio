import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.OneAddSmulVecMulVecMulVec
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsNatMulIsIntegralIwasawaDecompositionStatement

open ReciprocityTheory.ChartRestriction.G.FD NumberField GlobalTheory.UnipKill

namespace GlobalTheory.UnipKill

theorem exists_isotropic_partner (E : Type) [Field E] [NumberField E] [IsCMField E] (N : ℕ)
    (X : Data E N) (ξ : Fin N → E) (hξΛ : ξ ∈ X.Λ) (hξ : ξ ≠ 0) (hξξ : herm X.Gm ξ ξ = 0) :
    ∃ (η : Fin N → E) (d : ℕ), 0 < d ∧ η ∈ X.Λ ∧ herm X.Gm ξ η = d ∧ herm X.Gm η η = 0 := by
  have hG := X.Gm_herm
  obtain ⟨y, hy⟩ : ∃ y, herm X.Gm ξ y ≠ 0 := by
    by_contra hno
    push_neg at hno
    exact hξ (eq_zero_of_herm X.Gm X.Gm_det ξ hno)
  have h1 : herm X.Gm ξ ((cc (herm X.Gm ξ y))⁻¹ • y) = 1 := by
    rw [herm_smul_right, cc_inv, cc_cc]; exact inv_mul_cancel₀ hy
  obtain ⟨y1, hy1⟩ : ∃ y1, y1 = (cc (herm X.Gm ξ y))⁻¹ • y := ⟨_, rfl⟩
  rw [← hy1] at h1
  have h1' : herm X.Gm y1 ξ = 1 := by
    rw [← cc_herm X.Gm hG, h1, cc_one]
  have hhc : cc (herm X.Gm y1 y1) = herm X.Gm y1 y1 := cc_herm X.Gm hG y1 y1
  have hhalf : cc (herm X.Gm y1 y1 / 2) = herm X.Gm y1 y1 / 2 := by
    rw [div_eq_mul_inv, cc_mul, cc_inv, cc_two, hhc]
  have e1 : herm X.Gm ξ (y1 - (herm X.Gm y1 y1 / 2) • ξ) = 1 := by
    rw [herm_sub_right, herm_smul_right, h1, hξξ]; ring
  have e2 : herm X.Gm (y1 - (herm X.Gm y1 y1 / 2) • ξ) (y1 - (herm X.Gm y1 y1 / 2) • ξ) = 0 := by
    rw [herm_sub_left, herm_sub_right, herm_sub_right, herm_smul_right, herm_smul_right,
      herm_smul_left, herm_smul_left, h1, h1', hξξ, hhalf]
    ring
  obtain ⟨d, hd, hdΛ⟩ := GlobalTheory.T.exists_nat_smul_mem_lattice' E N X (y1 - (herm X.Gm y1 y1 / 2) • ξ)
  refine ⟨(d : E) • (y1 - (herm X.Gm y1 y1 / 2) • ξ), d, hd, hdΛ, ?_, ?_⟩
  · rw [herm_smul_right, cc_natCast, e1, mul_one]
  · rw [herm_smul_left, herm_smul_right, e2]; ring

end GlobalTheory.UnipKill
