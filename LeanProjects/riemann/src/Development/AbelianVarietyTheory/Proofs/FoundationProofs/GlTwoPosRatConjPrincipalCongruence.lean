import Development.AbelianVarietyTheory.Definitions.Divisors.ZetaActRefl
import Development.AbelianVarietyTheory.Definitions.Foundations.MemRingOfInR
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModQPrin
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModJTau
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

noncomputable section

namespace GlobalTheory.FN

open Matrix CongruenceSubgroup

set_option backward.isDefEq.respectTransparency false in

theorem conj_Gamma_den_mul (g : GL (Fin 2) ℚ) (M : ℕ) (y : SL(2, ℤ))
    (hy' : y ∈ Gamma ((g.1.den * (g⁻¹).1.den) * M)) :
    ∃ z ∈ Gamma M, ((z : Matrix (Fin 2) (Fin 2) ℤ).map (Int.cast : ℤ → ℚ)) =
      g.1 * ((y : Matrix (Fin 2) (Fin 2) ℤ).map (Int.cast : ℤ → ℚ)) * (g⁻¹).1 := by
  obtain ⟨y, hy⟩ := y
  let A₁ := g.1
  let A₂ := (g⁻¹).1
  have hA₁₂ : A₁ * A₂ = 1 := by simp only [← Matrix.GeneralLinearGroup.coe_mul,
    mul_inv_cancel, Matrix.GeneralLinearGroup.coe_one, A₁, A₂]
  let a₁ := A₁.den
  let a₂ := A₂.den
  obtain ⟨k, hk⟩ : ∃ k, y = 1 + (a₁ * a₂ * M) • k := by
    replace hy' : y.map (Int.cast : ℤ → ZMod (a₁ * a₂ * M)) = 1 := by
      rw [CongruenceSubgroup.Gamma_mem', Subtype.ext_iff] at hy'
      simpa using! hy'
    use Matrix.of fun i j ↦ (y - 1) i j / (a₁ * a₂ * M)
    rw [← sub_eq_iff_eq_add']
    ext i j
    simp_rw [Matrix.smul_apply, Matrix.of_apply, nsmul_eq_mul, Nat.cast_mul]
    refine (Int.mul_ediv_cancel_of_dvd ?_).symm
    rw [← Matrix.map_one Int.cast (by simp) (by simp), ← sub_eq_zero,
      ← Matrix.map_sub _ (by simp)] at hy'
    simpa only [Matrix.zero_apply, Matrix.map_apply, ZMod.intCast_zmod_eq_zero_iff_dvd,
      Nat.cast_mul] using! congr_fun₂ hy' i j
  let z := 1 + M • (A₁.num * k * A₂.num)
  have hz_coe : z.map Int.cast = A₁ * (y.map Int.cast) * A₂ := by
    simp only [Matrix.map_add _ Int.cast_add, Matrix.map_one _ Int.cast_zero Int.cast_one, hk,
      mul_add, mul_one, add_mul, hA₁₂, add_right_inj, z]
    conv_rhs => rw [← A₁.inv_denom_smul_num, ← A₂.inv_denom_smul_num, Matrix.map_smul _ _ (by simp)]
    simp only [Matrix.smul_mul, Matrix.mul_smul, Matrix.map_smul (Int.cast : ℤ → ℚ) M (by simp),
      Matrix.map_mul_intCast]
    rw [← Nat.cast_smul_eq_nsmul ℚ (_ * M), ← mul_smul, ← mul_smul,
      mul_comm a₁ a₂, Nat.cast_mul, Nat.cast_mul, mul_assoc _ _ (M : ℚ), mul_comm _ (M : ℚ),
      inv_mul_cancel_left₀ (mod_cast A₂.den_ne_zero),
      mul_inv_cancel_right₀ (mod_cast A₁.den_ne_zero), Nat.cast_smul_eq_nsmul]
  have hz_det : z.det = 1 := by
    have := congr_arg Matrix.det hz_coe
    simp_rw [Matrix.det_mul, ← Int.cast_det] at this
    rwa [mul_right_comm, ← Matrix.det_mul, hA₁₂, Matrix.det_one, one_mul, hy, Int.cast_inj] at this
  refine ⟨⟨z, hz_det⟩, ?_, hz_coe⟩
  rw [CongruenceSubgroup.Gamma_mem', Subtype.ext_iff]
  ext i j
  simp_rw [Matrix.SpecialLinearGroup.map_apply_coe, z, map_add, map_one, RingHom.mapMatrix_apply, Int.coe_castRingHom,
    Matrix.add_apply, map_apply, Matrix.SpecialLinearGroup.coe_one, add_eq_left, Matrix.smul_apply, nsmul_eq_mul,
    Int.cast_mul, Int.cast_natCast, ZMod.natCast_self M, zero_mul]

theorem exists_conj_principal_congruence :
    ∀ g : GQ, ∃ n : ℕ, 0 < n ∧ ∀ N : ℕ, ∀ δ ∈ CongruenceSubgroup.Gamma (N * n),
      ∃ δ' ∈ CongruenceSubgroup.Gamma N, g * ofSL δ = ofSL δ' * g := by
  intro g
  let G : GL (Fin 2) ℚ := g
  refine ⟨G.1.den * (G⁻¹).1.den, Nat.mul_pos (Nat.pos_of_ne_zero (Matrix.den_ne_zero _)) (Nat.pos_of_ne_zero (Matrix.den_ne_zero _)), fun N δ hδ => ?_⟩
  rw [mul_comm] at hδ
  obtain ⟨z, hz, hzc⟩ := conj_Gamma_den_mul G N δ hδ
  refine ⟨z, hz, ?_⟩
  apply Subtype.ext
  apply Units.ext
  have h21 : (G⁻¹).1 * G.1 = 1 := by
    simp only [← Matrix.GeneralLinearGroup.coe_mul, inv_mul_cancel,
      Matrix.GeneralLinearGroup.coe_one]
  show G.1 * ((δ : Matrix (Fin 2) (Fin 2) ℤ).map (Int.castRingHom ℚ)) =
    ((z : Matrix (Fin 2) (Fin 2) ℤ).map (Int.castRingHom ℚ)) * G.1
  have e1 : ((z : Matrix (Fin 2) (Fin 2) ℤ).map (Int.castRingHom ℚ)) =
      ((z : Matrix (Fin 2) (Fin 2) ℤ).map (Int.cast : ℤ → ℚ)) := rfl
  have e2 : ((δ : Matrix (Fin 2) (Fin 2) ℤ).map (Int.castRingHom ℚ)) =
      ((δ : Matrix (Fin 2) (Fin 2) ℤ).map (Int.cast : ℤ → ℚ)) := rfl
  rw [e1, e2, hzc, Matrix.mul_assoc, h21, Matrix.mul_one]

end GlobalTheory.FN
