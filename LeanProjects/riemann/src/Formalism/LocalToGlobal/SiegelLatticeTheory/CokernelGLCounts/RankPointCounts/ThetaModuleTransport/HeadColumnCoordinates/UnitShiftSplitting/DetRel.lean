import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.UnitShiftSplitting.HSmulSubRight

noncomputable section

open ValuativeRel Formalism.MainNotions.S.Loc Formalism.L2.SG.LsDatumA Formalism.L2.SG.LocalCountModules.LocCntCommon

namespace Formalism.L2.SG.LocalCountModules.UnitaryGroupMassFormula.LocCntUG

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
variable {M : Model F E}

theorem rel_smul_corner {R : Type} [CommRing R] {r : ℕ} (B₁ B₂ : Matrix (Fin (r + 1)) (Fin (r + 1)) R)
    (s c : R) (hrel : (B₁.submatrix Fin.castSucc Fin.castSucc).det * B₂.det =
      (B₂.submatrix Fin.castSucc Fin.castSucc).det * B₁.det) :
    ((s • B₁ + cornerM r c).submatrix Fin.castSucc Fin.castSucc).det * (s • B₂ + cornerM r c).det =
      ((s • B₂ + cornerM r c).submatrix Fin.castSucc Fin.castSucc).det * (s • B₁ + cornerM r c).det := by
  have hsub : ∀ B : Matrix (Fin (r + 1)) (Fin (r + 1)) R,
      (s • B).submatrix Fin.castSucc Fin.castSucc = s • B.submatrix Fin.castSucc Fin.castSucc := fun B => by
    ext a b; simp
  rw [det_add_cornerM, det_add_cornerM, head_add_cornerM, head_add_cornerM, hsub, hsub, Matrix.det_smul, Matrix.det_smul, Matrix.det_smul, Matrix.det_smul]
  simp only [Fintype.card_fin]
  linear_combination (s ^ r * s ^ (r + 1)) * hrel

theorem rel_transpose {R : Type} [CommRing R] {r : ℕ} (B₁ B₂ : Matrix (Fin (r + 1)) (Fin (r + 1)) R)
    (hrel : (B₁.submatrix Fin.castSucc Fin.castSucc).det * B₂.det =
      (B₂.submatrix Fin.castSucc Fin.castSucc).det * B₁.det) :
    (B₁.transpose.submatrix Fin.castSucc Fin.castSucc).det * B₂.transpose.det =
      (B₂.transpose.submatrix Fin.castSucc Fin.castSucc).det * B₁.transpose.det := by
  rw [← Matrix.transpose_submatrix, ← Matrix.transpose_submatrix]
  simp only [Matrix.det_transpose]
  exact hrel

theorem det_rel_split {g : SplitG M.L} (hs : M.split = some g) {r : ℕ}
    (Zh₁ Zh₂ : Matrix (Fin (r + 1)) (Fin (r + 1)) E) (T T' : F)
    (hrel : (Zh₁.submatrix Fin.castSucc Fin.castSucc).det * Zh₂.det =
      (Zh₂.submatrix Fin.castSucc Fin.castSucc).det * Zh₁.det) :
    ((HermSp.ZZplusOf M Zh₁ T T').submatrix Fin.castSucc Fin.castSucc).det * (HermSp.ZZplusOf M Zh₂ T T').det =
      ((HermSp.ZZplusOf M Zh₂ T T').submatrix Fin.castSucc Fin.castSucc).det *
        (HermSp.ZZplusOf M Zh₁ T T').det := by
  let φ₁ : E →+* F := (RingHom.fst F F).comp g.e.toRingEquiv.toRingHom
  let φ₂ : E →+* F := (RingHom.snd F F).comp g.e.toRingEquiv.toRingHom
  have hφ₁ : ∀ x, φ₁ x = (g.e x).1 := fun _ => rfl
  have hφ₂ : ∀ x, φ₂ x = (g.e x).2 := fun _ => rfl
  have hdet : ∀ (φ : E →+* F) (A : Matrix (Fin (r + 1)) (Fin (r + 1)) E), φ A.det = (A.map φ).det := by
    intro φ A; rw [RingHom.map_det]; rfl
  have hhd : ∀ (φ : E →+* F) (A : Matrix (Fin (r + 1)) (Fin (r + 1)) E),
      φ (A.submatrix Fin.castSucc Fin.castSucc).det = ((A.map φ).submatrix Fin.castSucc Fin.castSucc).det := by
    intro φ A; rw [RingHom.map_det]; rfl
  have hrelφ : ∀ φ : E →+* F, ((Zh₁.map φ).submatrix Fin.castSucc Fin.castSucc).det * (Zh₂.map φ).det =
      ((Zh₂.map φ).submatrix Fin.castSucc Fin.castSucc).det * (Zh₁.map φ).det := by
    intro φ
    rw [← hdet, ← hdet, ← hhd, ← hhd, ← map_mul, ← map_mul, hrel]
  have m1 : ∀ Zh : Matrix (Fin (r + 1)) (Fin (r + 1)) E,
      (HermSp.ZZplusOf M Zh T T').map φ₁ = ((g.q : F)⁻¹) • Zh.map φ₁ + cornerM r (T / (g.q : F)) := by
    intro Zh
    ext a b
    unfold HermSp.ZZplusOf
    rw [hs]
    simp only [Matrix.map_apply, Matrix.of_apply, Matrix.add_apply, Matrix.smul_apply, cornerM, smul_eq_mul,
      hφ₁, map_sub, AlgEquiv.apply_symm_apply, Prod.fst_sub]
    split_ifs with h
    · simp only [map_sub, AlgEquiv.apply_symm_apply, Prod.fst_sub]; ring
    · simp only [map_zero, Prod.fst_zero]; ring
  have m2 : ∀ Zh : Matrix (Fin (r + 1)) (Fin (r + 1)) E,
      (HermSp.ZZplusOf M Zh T T').map φ₂ = (-(g.q : F)⁻¹) • (Zh.map φ₂).transpose +
        cornerM r (-(T' / (g.q : F))) := by
    intro Zh
    ext a b
    unfold HermSp.ZZplusOf
    rw [hs]
    simp only [Matrix.map_apply, Matrix.of_apply, Matrix.add_apply, Matrix.smul_apply, cornerM, smul_eq_mul,
      hφ₂, Matrix.transpose_apply, map_sub, AlgEquiv.apply_symm_apply, Prod.snd_sub]
    split_ifs with h
    · simp only [map_sub, AlgEquiv.apply_symm_apply, Prod.snd_sub]; ring
    · simp only [map_zero, Prod.snd_zero]; ring
  apply g.e.injective
  refine Prod.ext ?_ ?_
  · show φ₁ _ = φ₁ _
    rw [map_mul, map_mul, hdet, hdet, hhd, hhd, m1, m1]
    exact rel_smul_corner _ _ _ _ (hrelφ φ₁)
  · show φ₂ _ = φ₂ _
    rw [map_mul, map_mul, hdet, hdet, hhd, hhd, m2, m2]
    exact rel_smul_corner _ _ _ _ (rel_transpose _ _ (hrelφ φ₂))

end Formalism.L2.SG.LocalCountModules.UnitaryGroupMassFormula.LocCntUG
