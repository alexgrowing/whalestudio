import Development.AbelianVarietyTheory.Definitions.Foundations.IsDCReps
open GlobalTheory.HeckeFamilyMatrices Polynomial UpperHalfPlane
open scoped MatrixGroups ModularForm
open scoped Manifold

namespace GlobalTheory.HeckeFamilyMatrices

theorem diam_conj_mem (N l : ℕ) (d : ZMod N) (σ : SL(2, ℤ)) (hσ : IsDiam N l d σ) (γ : SL(2, ℤ))
    (hγ : γ ∈ Lev N l) : σ * γ * σ⁻¹ ∈ Lev N l := by
  obtain ⟨hσ0, -⟩ := hσ
  rw [Lev, Subgroup.mem_inf] at hγ ⊢
  obtain ⟨hγ1, hγ0⟩ := hγ
  rw [CongruenceSubgroup.Gamma0_mem] at hσ0
  have hσl : σ ∈ CongruenceSubgroup.Gamma0 l := by
    rw [CongruenceSubgroup.Gamma0_mem]
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at hσ0 ⊢
    exact dvd_trans (by exact_mod_cast Dvd.intro_left N rfl) hσ0
  have hσN : ((σ 1 0 : ℤ) : ZMod N) = 0 := by
    rw [ZMod.intCast_zmod_eq_zero_iff_dvd] at hσ0 ⊢
    exact dvd_trans (by exact_mod_cast Dvd.intro l rfl) hσ0
  refine ⟨?_, ?_⟩
  · rw [CongruenceSubgroup.Gamma1_mem] at hγ1 ⊢
    obtain ⟨h00, h11, h10⟩ := hγ1
    have hdet := σ.2
    rw [Matrix.det_fin_two] at hdet
    have hdet' : ((σ 0 0 : ℤ) : ZMod N) * ((σ 1 1 : ℤ) : ZMod N) - ((σ 0 1 : ℤ) : ZMod N) * ((σ 1 0 : ℤ) : ZMod N) = 1 := by
      exact_mod_cast congrArg (Int.cast : ℤ → ZMod N) hdet
    simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two,
      Matrix.mul_apply, Fin.sum_univ_two, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one, Int.cast_add, Int.cast_mul, Int.cast_neg]
    set a : ZMod N := ((σ 0 0 : ℤ) : ZMod N)
    set b : ZMod N := ((σ 0 1 : ℤ) : ZMod N)
    set c : ZMod N := ((σ 1 0 : ℤ) : ZMod N)
    set e : ZMod N := ((σ 1 1 : ℤ) : ZMod N)
    set p : ZMod N := ((γ 0 0 : ℤ) : ZMod N)
    set q : ZMod N := ((γ 0 1 : ℤ) : ZMod N)
    set r : ZMod N := ((γ 1 0 : ℤ) : ZMod N)
    set s : ZMod N := ((γ 1 1 : ℤ) : ZMod N)
    refine ⟨?_, ?_, ?_⟩
    · linear_combination hdet' + a * e * h00 + b * e * h10 - a * q * hσN - b * c * h11
    · linear_combination hdet' + a * e * h11 - b * c * h00 - b * e * h10 + a * q * hσN
    · linear_combination e * p * hσN + e * e * h10 - c * q * hσN - e * s * hσN
  · exact (CongruenceSubgroup.Gamma0 l).mul_mem ((CongruenceSubgroup.Gamma0 l).mul_mem hσl hγ0)
      ((CongruenceSubgroup.Gamma0 l).inv_mem hσl)

theorem diam_normalises_lev : ∀ (N l : ℕ) (d : ZMod N) (σ : SL(2, ℤ)), IsDiam N l d σ →
    ∀ γ : Lev N l, ∃ γ' : Lev N l, mat σ * mat γ = mat γ' * mat σ := by
  intro N l d σ hσ γ
  refine ⟨⟨σ * (γ : SL(2, ℤ)) * σ⁻¹, diam_conj_mem N l d σ hσ γ γ.2⟩, ?_⟩
  simp only [mat, ← Matrix.SpecialLinearGroup.coe_mul, inv_mul_cancel_right]

end GlobalTheory.HeckeFamilyMatrices
