import Development.AbelianVarietyTheory.Definitions.Foundations.PetEqRelIndexMulPetProd
open UpperHalfPlane ModularForm CongruenceSubgroup MeasureTheory
open scoped MatrixGroups ModularForm Manifold

namespace GlobalTheory.Hk

theorem uOp_eq_sum_slash (q : ℕ) (k : ℤ) (f : ℍ → ℂ) (hq : 0 < q) : GlobalTheory.Hk.uOp q f = ∑ j ∈ Finset.range q, f ∣[k] (Matrix.GeneralLinearGroup.map (Rat.castHom ℝ) (Matrix.GeneralLinearGroup.mkOfDetNeZero !![(1 : ℚ), (j : ℚ); 0, (q : ℚ)] (by simp [Matrix.det_fin_two_of]; exact_mod_cast hq.ne'))) := by
  funext z
  rw [Finset.sum_apply, uOp, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  set g := Matrix.GeneralLinearGroup.map (Rat.castHom ℝ) (Matrix.GeneralLinearGroup.mkOfDetNeZero !![(1 : ℚ), (j : ℚ); 0, (q : ℚ)] (by simp [Matrix.det_fin_two_of]; exact_mod_cast hq.ne')) with hg
  have hval : g.1 = !![(1 : ℝ), (j : ℝ); 0, (q : ℝ)] := by
    ext a b
    fin_cases a <;> fin_cases b <;> simp [hg]
  have hdet : g.det.val = (q : ℝ) := by
    rw [Matrix.GeneralLinearGroup.val_det_apply, hval]; simp
  have hpos : 0 < g.det.val := by rw [hdet]; exact_mod_cast hq
  have hq0 : (q : ℂ) ≠ 0 := by exact_mod_cast hq.ne'
  rw [slash_apply, σ, if_pos hpos, hdet, ← ofComplex_apply (g • z), coe_smul_of_det_pos hpos]
  simp [num, denom, hval]
  rw [zpow_sub_one₀ hq0]
  field_simp

end GlobalTheory.Hk
