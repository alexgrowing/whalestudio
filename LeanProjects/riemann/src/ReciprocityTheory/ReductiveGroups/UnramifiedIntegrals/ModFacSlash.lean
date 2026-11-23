import Mathlib
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModDefs
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModBasic

noncomputable section
open scoped BigOperators Classical UpperHalfPlane MatrixGroups CongruenceSubgroup Manifold
open ModularForm EisensteinSeries ModularFormClass UpperHalfPlane Formalism.L2.Th1.CM

namespace ReciprocityTheory.ChartRestriction.L1

theorem denom_SL_coe (γ : SL(2, ℤ)) (z : ℍ) :
    denom γ z = ((γ 1 0 : ℤ) : ℂ) * z + ((γ 1 1 : ℤ) : ℂ) := by
  first
  | rfl
  | simp [UpperHalfPlane.denom]
  | (simp [UpperHalfPlane.denom]; norm_cast)

theorem smul_SL_coe (γ : SL(2, ℤ)) (z : ℍ) :
    ((γ • z : ℍ) : ℂ) = (((γ 0 0 : ℤ) : ℂ) * z + ((γ 0 1 : ℤ) : ℂ)) /
      (((γ 1 0 : ℤ) : ℂ) * z + ((γ 1 1 : ℤ) : ℂ)) := by
  first
  | (rw [UpperHalfPlane.coe_smul, UpperHalfPlane.num, denom_SL_coe]; simp)
  | (rw [UpperHalfPlane.specialLinearGroup_apply]; simp)
  | simp [UpperHalfPlane.coe_smul, UpperHalfPlane.num, UpperHalfPlane.denom]

theorem pt_smul {t t' : ℕ × ℕ × ℕ} (ht : 0 < t.1 ∧ 0 < t.2.2) (ht' : 0 < t'.1 ∧ 0 < t'.2.2)
    (γ γ' : SL(2, ℤ))
    (h : Tmat t * (γ : Matrix (Fin 2) (Fin 2) ℤ) = (γ' : Matrix (Fin 2) (Fin 2) ℤ) * Tmat t') (τ : ℍ) :
    pt t.1 t.2.1 t.2.2 (γ • τ) = γ' • pt t'.1 t'.2.1 t'.2.2 τ ∧
      denom γ' (pt t'.1 t'.2.1 t'.2.2 τ) * (t'.2.2 : ℂ) = (t.2.2 : ℂ) * denom γ τ := by
  have hm : ∀ i j, (Tmat t * (γ : Matrix (Fin 2) (Fin 2) ℤ)) i j =
      ((γ' : Matrix (Fin 2) (Fin 2) ℤ) * Tmat t') i j := fun i j => by rw [h]
  have z00 : (t.1 : ℤ) * γ 0 0 + (t.2.1 : ℤ) * γ 1 0 = γ' 0 0 * (t'.1 : ℤ) := by
    have hh := hm 0 0
    simp [Tmat, Matrix.mul_apply, Fin.sum_univ_two] at hh
    linarith
  have z01 : (t.1 : ℤ) * γ 0 1 + (t.2.1 : ℤ) * γ 1 1 = γ' 0 0 * (t'.2.1 : ℤ) + γ' 0 1 * (t'.2.2 : ℤ) := by
    have hh := hm 0 1
    simp [Tmat, Matrix.mul_apply, Fin.sum_univ_two] at hh
    linarith
  have z10 : (t.2.2 : ℤ) * γ 1 0 = γ' 1 0 * (t'.1 : ℤ) := by
    have hh := hm 1 0
    simp [Tmat, Matrix.mul_apply, Fin.sum_univ_two] at hh
    linarith
  have z11 : (t.2.2 : ℤ) * γ 1 1 = γ' 1 0 * (t'.2.1 : ℤ) + γ' 1 1 * (t'.2.2 : ℤ) := by
    have hh := hm 1 1
    simp [Tmat, Matrix.mul_apply, Fin.sum_univ_two] at hh
    linarith
  have c00 : (t.1 : ℂ) * ((γ 0 0 : ℤ) : ℂ) + (t.2.1 : ℂ) * ((γ 1 0 : ℤ) : ℂ) = ((γ' 0 0 : ℤ) : ℂ) * (t'.1 : ℂ) := by exact_mod_cast z00
  have c01 : (t.1 : ℂ) * ((γ 0 1 : ℤ) : ℂ) + (t.2.1 : ℂ) * ((γ 1 1 : ℤ) : ℂ) = ((γ' 0 0 : ℤ) : ℂ) * (t'.2.1 : ℂ) + ((γ' 0 1 : ℤ) : ℂ) * (t'.2.2 : ℂ) := by exact_mod_cast z01
  have c10 : (t.2.2 : ℂ) * ((γ 1 0 : ℤ) : ℂ) = ((γ' 1 0 : ℤ) : ℂ) * (t'.1 : ℂ) := by exact_mod_cast z10
  have c11 : (t.2.2 : ℂ) * ((γ 1 1 : ℤ) : ℂ) = ((γ' 1 0 : ℤ) : ℂ) * (t'.2.1 : ℂ) + ((γ' 1 1 : ℤ) : ℂ) * (t'.2.2 : ℂ) := by exact_mod_cast z11
  have he : (t.2.2 : ℂ) ≠ 0 := by exact_mod_cast ht.2.ne'
  have he' : (t'.2.2 : ℂ) ≠ 0 := by exact_mod_cast ht'.2.ne'
  have hD : ((γ 1 0 : ℤ) : ℂ) * (τ : ℂ) + ((γ 1 1 : ℤ) : ℂ) ≠ 0 := by rw [← denom_SL_coe]; exact UpperHalfPlane.denom_ne_zero _ _
  have hD' : ((γ' 1 0 : ℤ) : ℂ) * ((pt t'.1 t'.2.1 t'.2.2 τ : ℍ) : ℂ) + ((γ' 1 1 : ℤ) : ℂ) ≠ 0 := by rw [← denom_SL_coe]; exact UpperHalfPlane.denom_ne_zero _ _
  have hZ : ((γ • τ : ℍ) : ℂ) * (((γ 1 0 : ℤ) : ℂ) * (τ : ℂ) + ((γ 1 1 : ℤ) : ℂ)) = ((γ 0 0 : ℤ) : ℂ) * (τ : ℂ) + ((γ 0 1 : ℤ) : ℂ) := by
    rw [smul_SL_coe γ τ]; exact div_mul_cancel₀ _ hD
  have hW : ((pt t'.1 t'.2.1 t'.2.2 τ : ℍ) : ℂ) * (t'.2.2 : ℂ) = (t'.1 : ℂ) * (τ : ℂ) + (t'.2.1 : ℂ) := by
    rw [pt_coe ht'.1 ht'.2]; exact div_mul_cancel₀ _ he'
  have c2 : (((γ' 1 0 : ℤ) : ℂ) * ((pt t'.1 t'.2.1 t'.2.2 τ : ℍ) : ℂ) + ((γ' 1 1 : ℤ) : ℂ)) * (t'.2.2 : ℂ) = (t.2.2 : ℂ) * (((γ 1 0 : ℤ) : ℂ) * (τ : ℂ) + ((γ 1 1 : ℤ) : ℂ)) := by
    linear_combination ((γ' 1 0 : ℤ) : ℂ) * hW - (τ : ℂ) * c10 - c11
  refine ⟨UpperHalfPlane.ext ?_, ?_⟩
  · rw [pt_coe ht.1 ht.2, smul_SL_coe γ' (pt t'.1 t'.2.1 t'.2.2 τ), div_eq_div_iff he hD']
    have key : ((t'.2.2 : ℂ) * (((γ 1 0 : ℤ) : ℂ) * (τ : ℂ) + ((γ 1 1 : ℤ) : ℂ))) *
        (((t.1 : ℂ) * ((γ • τ : ℍ) : ℂ) + (t.2.1 : ℂ)) * (((γ' 1 0 : ℤ) : ℂ) * ((pt t'.1 t'.2.1 t'.2.2 τ : ℍ) : ℂ) + ((γ' 1 1 : ℤ) : ℂ)) - (((γ' 0 0 : ℤ) : ℂ) * ((pt t'.1 t'.2.1 t'.2.2 τ : ℍ) : ℂ) + ((γ' 0 1 : ℤ) : ℂ)) * (t.2.2 : ℂ)) = 0 := by
      linear_combination (((t.1 : ℂ) * ((γ • τ : ℍ) : ℂ) + (t.2.1 : ℂ)) * (((γ 1 0 : ℤ) : ℂ) * (τ : ℂ) + ((γ 1 1 : ℤ) : ℂ))) * c2 +
        ((t.2.2 : ℂ) * (((γ 1 0 : ℤ) : ℂ) * (τ : ℂ) + ((γ 1 1 : ℤ) : ℂ))) * ((t.1 : ℂ) * hZ - ((γ' 0 0 : ℤ) : ℂ) * hW + (τ : ℂ) * c00 + c01)
    rcases mul_eq_zero.mp key with h0 | h0
    · exact absurd h0 (mul_ne_zero he' hD)
    · exact sub_eq_zero.mp h0
  · rw [denom_SL_coe, denom_SL_coe]
    exact c2

theorem fac_smul {t t' : ℕ × ℕ × ℕ} (ht : 0 < t.1 ∧ 0 < t.2.2) (ht' : 0 < t'.1 ∧ 0 < t'.2.2)
    (γ γ' : SL(2, ℤ))
    (h : Tmat t * (γ : Matrix (Fin 2) (Fin 2) ℤ) = (γ' : Matrix (Fin 2) (Fin 2) ℤ) * Tmat t') (τ : ℍ) :
    fac t (γ • τ) = denom γ τ ^ 24 * ((t.2.2 : ℂ) / t'.2.2) ^ 12 * fac t' τ := by
  obtain ⟨h1, h2⟩ := pt_smul ht ht' γ γ' h τ
  have he' : ((t'.2.2 : ℕ) : ℂ) ≠ 0 := by exact_mod_cast ht'.2.ne'
  have hd : denom γ' (pt t'.1 t'.2.1 t'.2.2 τ) = (t.2.2 : ℂ) / t'.2.2 * denom γ τ := by
    rw [div_mul_eq_mul_div, eq_div_iff he']
    exact h2
  simp only [fac]
  rw [h1, AA_smul, DD_smul, AA_smul, DD_smul, hd]
  ring

end ReciprocityTheory.ChartRestriction.L1
