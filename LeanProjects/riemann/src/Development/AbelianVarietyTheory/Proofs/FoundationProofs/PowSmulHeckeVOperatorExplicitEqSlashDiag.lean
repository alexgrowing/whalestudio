import Development.AbelianVarietyTheory.Definitions.Foundations.PetEqRelIndexMulPetProd

open UpperHalfPlane ModularForm CongruenceSubgroup MeasureTheory
open scoped MatrixGroups ModularForm Manifold

namespace GlobalTheory.Hk

theorem smul_vOp_eq_slash (q : ℕ) (k : ℤ) (f : ℍ → ℂ) (hq : 0 < q) : (q : ℂ) ^ (k - 1) • vOp q f = f ∣[k] (Matrix.GeneralLinearGroup.map (Rat.castHom ℝ) (Matrix.GeneralLinearGroup.mkOfDetNeZero !![(q : ℚ), 0; 0, 1] (by simp [Matrix.det_fin_two_of]; exact_mod_cast hq.ne'))) := by
  set g := (Matrix.GeneralLinearGroup.map (Rat.castHom ℝ) (Matrix.GeneralLinearGroup.mkOfDetNeZero !![(q : ℚ), 0; 0, 1] (by simp [Matrix.det_fin_two_of]; exact_mod_cast hq.ne'))) with hg
  have h00 : (g : Matrix (Fin 2) (Fin 2) ℝ) 0 0 = q := by simp [hg, Matrix.GeneralLinearGroup.mkOfDetNeZero]
  have h01 : (g : Matrix (Fin 2) (Fin 2) ℝ) 0 1 = 0 := by simp [hg, Matrix.GeneralLinearGroup.mkOfDetNeZero]
  have h10 : (g : Matrix (Fin 2) (Fin 2) ℝ) 1 0 = 0 := by simp [hg, Matrix.GeneralLinearGroup.mkOfDetNeZero]
  have h11 : (g : Matrix (Fin 2) (Fin 2) ℝ) 1 1 = 1 := by simp [hg, Matrix.GeneralLinearGroup.mkOfDetNeZero]
  have hdet : (g.det : ℝ) = q := by
    rw [Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_fin_two, h00, h01, h10, h11]; ring
  have hdpos : 0 < (g.det : ℝ) := by rw [hdet]; exact_mod_cast hq
  ext τ
  have hden : denom g τ = 1 := by simp [denom, h10, h11]
  have hnum : num g τ = q * τ := by simp [num, h00, h01]
  have hsmul : ((g • τ : ℍ) : ℂ) = q * τ := by
    rw [UpperHalfPlane.coe_smul_of_det_pos hdpos, hnum, hden, div_one]
  have hof : ofComplex ((q : ℂ) * τ) = g • τ := by
    rw [← hsmul]; exact ofComplex_apply _
  rw [slash_apply, hden, one_zpow, mul_one, hdet, abs_of_pos (by exact_mod_cast hq : (0:ℝ) < q)]
  simp only [σ, hdpos, if_true, RingHom.id_apply, Pi.smul_apply, smul_eq_mul, vOp, hof]
  push_cast
  ring_nf
  rfl

end GlobalTheory.Hk
