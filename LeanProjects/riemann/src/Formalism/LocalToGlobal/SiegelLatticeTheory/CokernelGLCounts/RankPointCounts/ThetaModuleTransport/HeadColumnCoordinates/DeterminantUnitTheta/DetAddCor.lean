import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.DeterminantUnitTheta.Development

noncomputable section

open ValuativeRel Formalism.MainNotions.S.Loc Formalism.L2.SG.LsDatumA Formalism.L2.SG.LocalCountModules.LocCntCommon

namespace Formalism.L2.SG.LocalCountModules.ThetaMbe0GWork

theorem det_add_cor {K : Type} [CommRing K] {r : ℕ} (A : Matrix (Fin (r + 1)) (Fin (r + 1)) K) (c : K) :
    (A + Matrix.of fun a b => cor r a b c).det = A.det + c * (A.submatrix Fin.castSucc Fin.castSucc).det := by
  have e1 : A + Matrix.of (fun a b => cor r a b c) =
      A.updateRow (Fin.last r) (A (Fin.last r) + c • Pi.single (Fin.last r) 1) := by
    ext a b
    by_cases ha : a = Fin.last r
    · subst ha
      by_cases hb : b = Fin.last r
      · subst hb
        simp [cor]
      · simp [cor, hb, Pi.single_apply]
    · simp [cor, ha, Matrix.updateRow_ne ha]
  rw [e1, Matrix.det_updateRow_add, Matrix.updateRow_eq_self, Matrix.det_updateRow_smul]
  congr 2
  rw [Matrix.det_succ_row _ (Fin.last r), Finset.sum_eq_single (Fin.last r)]
  · have hsub : (A.updateRow (Fin.last r) (Pi.single (Fin.last r) 1)).submatrix (Fin.last r).succAbove
        (Fin.last r).succAbove = A.submatrix Fin.castSucc Fin.castSucc := by
      ext a b
      simp [Fin.succAbove_last, Matrix.updateRow_ne (Fin.castSucc_lt_last a).ne]
    rw [hsub, Matrix.updateRow_self, Pi.single_eq_same, mul_one, Fin.val_last, ← two_mul, pow_mul, neg_one_sq,
      one_pow, one_mul]
  · intro j _ hj
    rw [Matrix.updateRow_self, Pi.single_eq_of_ne hj, mul_zero, zero_mul]
  · simp

theorem detG_holds : DetG := by
  intro F _ _ _ E _ _ _ _ M g hs r Zh T T' hh hu
  let φ₁ : E →+* F := (RingHom.fst F F).comp g.e.toRingEquiv.toRingHom
  let φ₂ : E →+* F := (RingHom.snd F F).comp g.e.toRingEquiv.toRingHom
  have hφ₁ : ∀ x, φ₁ x = (g.e x).1 := fun _ => rfl
  have hφ₂ : ∀ x, φ₂ x = (g.e x).2 := fun _ => rfl
  have key : ∀ x : E, IsUnit x ↔ φ₁ x ≠ 0 ∧ φ₂ x ≠ 0 := by
    intro x
    rw [← isUnit_map_iff g.e x, Prod.isUnit_iff, isUnit_iff_ne_zero, isUnit_iff_ne_zero]
    rfl
  have hq : (g.q : F) ≠ 0 := by
    intro h
    exact g.q_irr.ne_zero (Subtype.ext h)
  set Zz := HermSp.ZZplusOf M Zh T T' with hZz
  have e1 : Zz.map φ₁ = (g.q : F)⁻¹ • Zh.map φ₁ + Matrix.of fun a b => cor r a b (T / (g.q : F)) := by
    ext a b
    rw [hZz]
    unfold HermSp.ZZplusOf
    rw [hs]
    by_cases h : a = Fin.last r ∧ b = Fin.last r
    · simp [hφ₁, cor, h, div_eq_inv_mul]
      try ring
    · simp [hφ₁, cor, h, div_eq_inv_mul]
  have e2 : Zz.map φ₂ = (-(g.q : F)⁻¹) • (Zh.map φ₂).transpose +
      Matrix.of fun a b => cor r a b (-(T' / (g.q : F))) := by
    ext a b
    rw [hZz]
    unfold HermSp.ZZplusOf
    rw [hs]
    by_cases h : a = Fin.last r ∧ b = Fin.last r
    · simp [hφ₂, cor, h, div_eq_inv_mul]
      try ring
    · simp [hφ₂, cor, h, div_eq_inv_mul]
  have hh1 : φ₁ ((Zh.submatrix Fin.castSucc Fin.castSucc).det) = 0 := by rw [hh, map_zero]
  have hh2 : φ₂ ((Zh.submatrix Fin.castSucc Fin.castSucc).det) = 0 := by rw [hh, map_zero]
  rw [RingHom.map_det, RingHom.mapMatrix_apply] at hh1 hh2
  obtain ⟨u1, u2⟩ := (key _).1 hu
  rw [RingHom.map_det, RingHom.mapMatrix_apply, e1, det_add_cor] at u1
  rw [RingHom.map_det, RingHom.mapMatrix_apply, e2, det_add_cor] at u2
  rw [key, RingHom.map_det, RingHom.map_det, RingHom.mapMatrix_apply, RingHom.mapMatrix_apply]
  constructor
  · intro h0
    apply u1
    have hs1 : (((g.q : F)⁻¹ • Zh.map φ₁).submatrix Fin.castSucc Fin.castSucc) =
        (g.q : F)⁻¹ • ((Zh.submatrix Fin.castSucc Fin.castSucc).map φ₁) := by
      ext a b; simp
    rw [Matrix.det_smul, h0, hs1, Matrix.det_smul, hh1]
    ring
  · intro h0
    apply u2
    have hs2 : ((-(g.q : F)⁻¹) • (Zh.map φ₂).transpose).submatrix Fin.castSucc Fin.castSucc =
        (-(g.q : F)⁻¹) • ((Zh.submatrix Fin.castSucc Fin.castSucc).map φ₂).transpose := by
      ext a b; simp
    rw [Matrix.det_smul, Matrix.det_transpose, h0, hs2, Matrix.det_smul, Matrix.det_transpose, hh2]
    ring

end Formalism.L2.SG.LocalCountModules.ThetaMbe0GWork
