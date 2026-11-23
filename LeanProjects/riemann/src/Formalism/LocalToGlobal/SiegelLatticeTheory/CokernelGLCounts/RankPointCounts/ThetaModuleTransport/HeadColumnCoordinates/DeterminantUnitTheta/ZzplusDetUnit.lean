import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.DeterminantUnitTheta.SplitIsoCountOfComponents
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.DeterminantUnitTheta.LeadingMinorSecondProj

noncomputable section

open ValuativeRel Formalism.MainNotions.S.Loc Formalism.L2.SG.LsDatumA Formalism.L2.SG.LocalCountModules.LocCntCommon

namespace Formalism.L2.SG.LocalCountModules.ThetaMbe0GWork

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
variable {M : Model F E} {g : SplitG M.L} {r : ℕ}

theorem zzplus_det_unit (hs : M.split = some g) (Zh : Matrix (Fin (r + 1)) (Fin (r + 1)) E) (T T' : F)
    (hu : IsUnit Zh.det) (h0 : (Zh.submatrix Fin.castSucc Fin.castSucc).det = 0) :
    IsUnit (HermSp.ZZplusOf M Zh T T').det := by
  have hne : ∀ i : Fin r, (Fin.castSucc i = Fin.last r) = False := fun i => eq_false (Fin.castSucc_ne_last i)
  have h1 : ((HermSp.ZZplusOf M Zh T T').submatrix Fin.castSucc Fin.castSucc).map (ph1 g) =
      ((g.q : F)⁻¹) • (Zh.submatrix Fin.castSucc Fin.castSucc).map (ph1 g) := by
    ext i j
    simp only [Matrix.map_apply, Matrix.submatrix_apply, Matrix.smul_apply, smul_eq_mul, firstProj_apply, zz_comp hs,
      hne, false_and, if_false, sub_zero]
    rw [div_eq_inv_mul]
  have h2 : ((HermSp.ZZplusOf M Zh T T').submatrix Fin.castSucc Fin.castSucc).map (ph2 g) =
      (-(g.q : F)⁻¹) • ((Zh.submatrix Fin.castSucc Fin.castSucc).map (ph2 g)).transpose := by
    ext i j
    simp only [Matrix.map_apply, Matrix.submatrix_apply, Matrix.smul_apply, Matrix.transpose_apply, smul_eq_mul,
      secondProj_apply, zz_comp hs, hne, false_and, if_false, sub_zero]
    rw [div_eq_inv_mul, neg_mul]
  have hS1 : ph1 g ((HermSp.ZZplusOf M Zh T T').submatrix Fin.castSucc Fin.castSucc).det = 0 := by
    rw [det_ph, h1, Matrix.det_smul, ← det_ph, h0, map_zero, mul_zero]
  have hS2 : ph2 g ((HermSp.ZZplusOf M Zh T T').submatrix Fin.castSucc Fin.castSucc).det = 0 := by
    rw [det_ph, h2, Matrix.det_smul, Matrix.det_transpose, ← det_ph, h0, map_zero, mul_zero]
  have hS : ((HermSp.ZZplusOf M Zh T T').submatrix Fin.castSucc Fin.castSucc).det = 0 := by
    apply g.e.injective
    rw [map_zero]
    refine Prod.ext ?_ ?_
    · rw [Prod.fst_zero, ← firstProj_apply]
      exact hS1
    · rw [Prod.snd_zero, ← secondProj_apply]
      exact hS2
  have hm : (ZZm g Zh T T').submatrix Fin.castSucc Fin.castSucc =
      (HermSp.ZZplusOf M Zh T T').submatrix Fin.castSucc Fin.castSucc := by
    ext i j
    simp only [ZZm, Matrix.submatrix_apply, Matrix.add_apply, Matrix.of_apply, cor, hne, false_and, if_false,
      add_zero]
  have key : HermSp.ZZplusOf M Zh T T' = ZZm g Zh T T' +
      Matrix.of fun a b => cor r a b (-(g.e.symm (-T / (g.q : F), T' / (g.q : F)))) := by
    ext a b
    simp only [ZZm, Matrix.add_apply, Matrix.of_apply, cor]
    split_ifs <;> ring
  rw [key, det_add_cor, hm, hS, mul_zero, add_zero]
  exact unit_zzm hs Zh T T' hu

end Formalism.L2.SG.LocalCountModules.ThetaMbe0GWork
