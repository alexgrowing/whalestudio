import Formalism.LocalToGlobal.TorsionIntegrality.UniformGaussModels.OrthogonalGaussModels.HermitianBlockFrames.AreaCmLNe
import Formalism.LocalToGlobal.TorsionIntegrality.UniformGaussModels.OrthogonalGaussModels.HermitianBlockFrames.MkLeOfDenseRange
import Formalism.LocalToGlobal.TorsionIntegrality.UniformGaussModels.OrthogonalGaussModels.HermitianBlockFrames.Inert57

noncomputable section
open scoped BigOperators ComplexConjugate

namespace Formalism.L2.Th1.Top.FrP.UnitaryGroupMassFormula.HermFrame
open Formalism.L2.Th1.Top.FrP

abbrev L7 : PeriodPair := cmL 1 1 7 (by norm_num) (by norm_num) 1 one_ne_zero

theorem period_lattice_disc_seven_first_period : L7.ω₁ = 1 := by simp [L7, cmL, scalePair, cmPair]
theorem period_lattice_disc_seven_second_period : L7.ω₂ = cmTheta 1 7 := by simp [L7, cmL, scalePair, cmPair]

theorem sqrt_seven_pos : 0 < Real.sqrt 7 := Real.sqrt_pos.mpr (by norm_num)

theorem area_discriminant_seven_lattice : area L7 = Real.sqrt 7 / 2 := by
  rw [area, period_lattice_disc_seven_first_period, period_lattice_disc_seven_second_period]
  simp [cmTheta, Complex.div_im]
  positivity

abbrev h7 : Matrix (Fin 1) (Fin 1) ℂ := (((area L7 : ℝ) : ℂ)⁻¹) • (1 : Matrix (Fin 1) (Fin 1) ℂ)

theorem block_diag_hermitian_form_disc_seven : blk4 h7 = (((area L7 : ℝ) : ℂ)⁻¹) • (1 : Matrix (Fin 4 × Fin 1) (Fin 4 × Fin 1) ℂ) := by
  ext ⟨a, i⟩ ⟨b, j⟩
  fin_cases i; fin_cases j
  by_cases hab : a = b
  · subst hab; simp [blk4, Matrix.one_apply]
  · simp [blk4, Matrix.one_apply, hab]

theorem theta7_sq : cmTheta 1 7 * cmTheta 1 7 = cmTheta 1 7 - 2 := by
  have h := sq_mul_sq 7
  simp only [cmTheta]
  have e : ((1 : ℤ) : ℂ) = 1 := by norm_num
  rw [e]
  have : Complex.I * ((Real.sqrt ((7 : ℕ) : ℝ) : ℝ) : ℂ) = sq 7 := rfl
  rw [this]
  push_cast at h ⊢
  linear_combination h / 4

theorem cmTheta_smul_mem_stdLat : ∀ x ∈ stdLat L7 (Fin 1), cmTheta 1 7 • x ∈ stdLat L7 (Fin 1) := by
  intro x hx
  refine (AddSubgroup.mem_pi _).mpr fun i _ => ?_
  obtain ⟨m, k, e⟩ := PeriodPair.mem_lattice.mp ((AddSubgroup.mem_pi _).mp hx i (Set.mem_univ _))
  rw [Pi.smul_apply, smul_eq_mul, ← e, period_lattice_disc_seven_first_period, period_lattice_disc_seven_second_period]
  refine PeriodPair.mem_lattice.mpr ⟨-2 * k, m + k, ?_⟩
  rw [period_lattice_disc_seven_first_period, period_lattice_disc_seven_second_period]
  have := theta7_sq
  push_cast
  linear_combination (-(k : ℂ)) * this

theorem theta7_re : (cmTheta 1 7).re = 1 / 2 := by simp [cmTheta, Complex.div_re]
theorem theta7_im : (cmTheta 1 7).im = Real.sqrt 7 / 2 := by simp [cmTheta, Complex.div_im]

theorem selfDualBis : IsSelfDual (matH h7) (stdLat L7 (Fin 1)) := by
  have hmat : matH h7 = stdH L7 (Fin 1) := rfl
  rw [IsSelfDual, hmat]
  ext x
  constructor
  · intro hx
    refine (AddSubgroup.mem_pi _).mpr fun i _ => ?_
    have hi : i = 0 := Subsingleton.elim _ _
    subst hi
    have hs2 : Real.sqrt 7 / 2 ≠ 0 := by have := sqrt_seven_pos; positivity
    have key : ∀ w : ℂ, altE (stdH L7 (Fin 1)) x (fun _ => w) = (x 0 * (starRingEnd ℂ) w).im / (Real.sqrt 7 / 2) := by
      intro w
      rw [altE, stdH_apply, Fin.sum_univ_one, area_discriminant_seven_lattice]
      have e : x 0 * ((Real.sqrt 7 / 2 : ℝ) : ℂ)⁻¹ * (starRingEnd ℂ) w
          = (((Real.sqrt 7 / 2)⁻¹ : ℝ) : ℂ) * (x 0 * (starRingEnd ℂ) w) := by push_cast; ring
      rw [e, Complex.im_ofReal_mul, div_eq_inv_mul]
      ring
    obtain ⟨m₁, hm₁⟩ := hx (fun _ => L7.ω₁) ((AddSubgroup.mem_pi _).mpr fun _ _ => L7.ω₁_mem_lattice)
    obtain ⟨m₂, hm₂⟩ := hx (fun _ => L7.ω₂) ((AddSubgroup.mem_pi _).mpr fun _ _ => L7.ω₂_mem_lattice)
    rw [key, div_eq_iff hs2, period_lattice_disc_seven_first_period] at hm₁
    rw [key, div_eq_iff hs2, period_lattice_disc_seven_second_period, Complex.mul_im, Complex.conj_re, Complex.conj_im, theta7_re, theta7_im] at hm₂
    simp only [map_one, mul_one] at hm₁
    refine PeriodPair.mem_lattice.mpr ⟨-m₂, m₁, ?_⟩
    rw [period_lattice_disc_seven_first_period, period_lattice_disc_seven_second_period]
    apply Complex.ext
    · simp only [Complex.add_re, Complex.mul_re, Complex.intCast_re, Complex.intCast_im, Complex.one_re,
        Complex.one_im, theta7_re, theta7_im, mul_one, mul_zero, sub_zero]
      have h : (Real.sqrt 7 / 2) * ((-m₂ : ℤ) + (m₁ : ℝ) * (1 / 2) - (x 0).re) = 0 := by
        push_cast
        linear_combination hm₂ - (1 / 2) * hm₁
      have := (mul_eq_zero.mp h).resolve_left hs2
      push_cast at this ⊢
      linarith
    · simp only [Complex.add_im, Complex.mul_im, Complex.intCast_re, Complex.intCast_im, Complex.one_re,
        Complex.one_im, theta7_re, theta7_im, mul_one, mul_zero, zero_mul, add_zero, zero_add]
      linarith
  · intro hx y hy
    exact stdLat_int L7 hx hy

theorem fourth_power_standard_lattice_disc_seven : pow4 (stdLat L7 (Fin 1)) = stdLat L7 (Fin 4 × Fin 1) := by
  ext z
  constructor
  · intro hz
    refine (AddSubgroup.mem_pi _).mpr fun w _ => ?_
    exact (AddSubgroup.mem_pi _).mp (hz w.1) w.2 (Set.mem_univ _)
  · intro hz a
    refine (AddSubgroup.mem_pi _).mpr fun i _ => ?_
    exact (AddSubgroup.mem_pi _).mp hz (a, i) (Set.mem_univ _)

theorem image_identity_standard_lattice_disc_seven :
    imgLat ((LinearEquiv.refl ℂ (Fin 4 × Fin 1 → ℂ)) : (Fin 4 × Fin 1 → ℂ) →ₗ[ℂ] (Fin 4 × Fin 1 → ℂ))
      (pow4 (stdLat L7 (Fin 1))) = stdLat L7 (Fin 4 × Fin 1) := by
  rw [fourth_power_standard_lattice_disc_seven]
  ext z
  simp [imgLat]

theorem relative_index_identity_lattice_disc_seven :
    relIdx (stdLat L7 (Fin 4 × Fin 1))
      (imgLat ((LinearEquiv.refl ℂ (Fin 4 × Fin 1 → ℂ)) : (Fin 4 × Fin 1 → ℂ) →ₗ[ℂ] (Fin 4 × Fin 1 → ℂ))
        (pow4 (stdLat L7 (Fin 1)))) = 1 := by
  rw [image_identity_standard_lattice_disc_seven, relIdx, AddSubgroup.relIndex_self]

theorem isometry_identity_hermitian_disc_seven : IsIsom (matH (blk4 h7)) (stdH L7 (Fin 4 × Fin 1))
    ((LinearEquiv.refl ℂ (Fin 4 × Fin 1 → ℂ)) : (Fin 4 × Fin 1 → ℂ) →ₗ[ℂ] (Fin 4 × Fin 1 → ℂ)) := by
  intro x y
  rw [block_diag_hermitian_form_disc_seven]
  rfl

theorem is_hermitian_lattice_disc_seven : IsLatH L7 1 7 h7 (stdLat L7 (Fin 1)) (LinearEquiv.refl ℂ (Fin 4 × Fin 1 → ℂ)) := by
  refine ⟨isometry_identity_hermitian_disc_seven, selfDualBis, cmTheta_smul_mem_stdLat, ?_, ?_⟩
  · rw [relative_index_identity_lattice_disc_seven]; norm_num
  · rw [image_identity_standard_lattice_disc_seven, relIdx, AddSubgroup.relIndex_self]; norm_num

theorem inhabitant_but_frobenius :
    CmOK 1 1 2 7 ∧ ¬ 5 ∣ 7 ∧ (¬ ∃ a : ZMod 5, a ^ 2 = -((7 : ℕ) : ZMod 5)) ∧
    (haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩; Nonempty (ℂ ≃+* ℂ_[5])) ∧
    IsLatH L7 1 7 h7 (stdLat L7 (Fin 1)) (LinearEquiv.refl ℂ (Fin 4 × Fin 1 → ℂ)) ∧
    IsIsom (matH (blk4 h7)) (stdH L7 (Fin 4 × Fin 1))
      ((LinearEquiv.refl ℂ (Fin 4 × Fin 1 → ℂ)) : (Fin 4 × Fin 1 → ℂ) →ₗ[ℂ] (Fin 4 × Fin 1 → ℂ)) ∧
    ¬ 5 ∣ relIdx (stdLat L7 (Fin 4 × Fin 1))
      (imgLat ((LinearEquiv.refl ℂ (Fin 4 × Fin 1 → ℂ)) : (Fin 4 × Fin 1 → ℂ) →ₗ[ℂ] (Fin 4 × Fin 1 → ℂ))
        (pow4 (stdLat L7 (Fin 1)))) := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  refine ⟨cmOK_7, by norm_num, inert_5_7, exists_iota 5, is_hermitian_lattice_disc_seven, isometry_identity_hermitian_disc_seven, ?_⟩
  rw [relative_index_identity_lattice_disc_seven]; norm_num

end Formalism.L2.Th1.Top.FrP.UnitaryGroupMassFormula.HermFrame
