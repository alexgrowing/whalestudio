import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.UnitShiftSplitting.SecondIsoComponentLinearOf

noncomputable section

open ValuativeRel Formalism.MainNotions.S.Loc Formalism.L2.SG.LsDatumA Formalism.L2.SG.LocalCountModules.LocCntCommon Formalism.L2.SG.LocalCountModules.ThetaMbe0GWork

namespace Formalism.L2.SG.LocalCountModules.AlgGSplit

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
variable {M : Model F E} {g : SplitG M.L} {r : ℕ}

def p1 (g : SplitG M.L) : E →+* F := (RingHom.fst F F).comp g.e.toRingEquiv.toRingHom

def p2 (g : SplitG M.L) : E →+* F := (RingHom.snd F F).comp g.e.toRingEquiv.toRingHom

theorem adeleInfiniteComponent_apply (x : E) : p1 g x = (g.e x).1 := rfl
theorem adele_ext_components (x : E) : p2 g x = (g.e x).2 := rfl

theorem map_inv_of {K : Type} [CommRing K] {n : Type} [Fintype n] [DecidableEq n] (f : E →+* K)
    (A : Matrix n n E) (hA : IsUnit A.det) : (A⁻¹).map f = (A.map f)⁻¹ := by
  symm
  apply Matrix.inv_eq_right_inv
  rw [← Matrix.map_mul, Matrix.mul_nonsing_inv _ hA, Matrix.map_one _ (map_zero f) (map_one f)]

theorem inv_last {K : Type} [CommRing K] (A : Matrix (Fin (r + 1)) (Fin (r + 1)) K) :
    A⁻¹ (Fin.last r) (Fin.last r) = Ring.inverse A.det * (A.submatrix Fin.castSucc Fin.castSucc).det := by
  rw [Matrix.inv_def, Matrix.smul_apply, Matrix.adjugate_fin_succ_eq_det_submatrix, Fin.succAbove_last]
  simp

theorem kap_common {Zh₁ Zh₂ : Matrix (Fin (r + 1)) (Fin (r + 1)) E} (hk : KapEq Zh₁ Zh₂)
    (h₁ : IsUnit Zh₁.det) (h₂ : IsUnit Zh₂.det) :
    Zh₁⁻¹ (Fin.last r) (Fin.last r) = Zh₂⁻¹ (Fin.last r) (Fin.last r) := by
  rw [inv_last, inv_last]
  obtain ⟨u₁, hu₁⟩ := h₁
  obtain ⟨u₂, hu₂⟩ := h₂
  unfold KapEq at hk
  rw [← hu₁, ← hu₂] at hk ⊢
  simp only [Ring.inverse_unit]
  apply (u₁ * u₂).isUnit.mul_left_cancel
  push_cast
  calc (u₁ : E) * u₂ * (↑u₁⁻¹ * (Zh₁.submatrix Fin.castSucc Fin.castSucc).det)
      = u₂ * (Zh₁.submatrix Fin.castSucc Fin.castSucc).det * (u₁ * ↑u₁⁻¹) := by ring
    _ = u₂ * (Zh₁.submatrix Fin.castSucc Fin.castSucc).det := by rw [Units.mul_inv, mul_one]
    _ = u₁ * (Zh₂.submatrix Fin.castSucc Fin.castSucc).det := hk.symm
    _ = u₁ * (Zh₂.submatrix Fin.castSucc Fin.castSucc).det * (u₂ * ↑u₂⁻¹) := by rw [Units.mul_inv, mul_one]
    _ = (u₁ : E) * u₂ * (↑u₂⁻¹ * (Zh₂.submatrix Fin.castSucc Fin.castSucc).det) := by ring

variable (hs : M.split = some g)
include hs

theorem zzMinus_firstProj (Zh : Matrix (Fin (r + 1)) (Fin (r + 1)) E) (T T' : F) :
    (ZZm g Zh T T').map (p1 g) = (g.q : F)⁻¹ • Zh.map (p1 g) := by
  ext b a
  simp only [ZZm, Matrix.map_apply, Matrix.add_apply, Matrix.of_apply, map_add, Matrix.smul_apply,
    smul_eq_mul, adeleInfiniteComponent_apply]
  rw [zz_comp hs, e_cor]
  simp only [ind, AlgEquiv.apply_symm_apply]
  split_ifs <;> ring

theorem zzMinus_secondProj (Zh : Matrix (Fin (r + 1)) (Fin (r + 1)) E) (T T' : F) :
    (ZZm g Zh T T').map (p2 g) = -(g.q : F)⁻¹ • (Zh.map (p2 g)).transpose := by
  ext b a
  simp only [ZZm, Matrix.map_apply, Matrix.add_apply, Matrix.of_apply, map_add, Matrix.smul_apply,
    smul_eq_mul, adele_ext_components, Matrix.transpose_apply]
  rw [zz_comp hs, e_cor]
  simp only [ind, AlgEquiv.apply_symm_apply]
  split_ifs <;> ring

theorem det_map_unit {n : Type} [Fintype n] [DecidableEq n] (f : E →+* F) (A : Matrix n n E)
    (hA : IsUnit A.det) : IsUnit (A.map f).det := by
  have := hA.map f
  rwa [RingHom.map_det] at this

theorem zm_unit {Zh : Matrix (Fin (r + 1)) (Fin (r + 1)) E} (hZh : IsUnit Zh.det) (T T' : F) :
    IsUnit (ZZm g Zh T T').det := by
  have hq := q_ne g
  apply Formalism.L2.SG.LocalCountModules.UnitaryGroupMassFormula.LocCntUG.isUnit_of_comp g
  · rw [← adeleInfiniteComponent_apply, RingHom.map_det]
    change (((ZZm g Zh T T').map (p1 g))).det ≠ 0
    rw [zzMinus_firstProj hs, Matrix.det_smul]
    exact mul_ne_zero (pow_ne_zero _ (inv_ne_zero hq)) (det_map_unit hs (p1 g) Zh hZh).ne_zero
  · rw [← adele_ext_components, RingHom.map_det]
    change (((ZZm g Zh T T').map (p2 g))).det ≠ 0
    rw [zzMinus_secondProj hs, Matrix.det_smul, Matrix.det_transpose]
    exact mul_ne_zero (pow_ne_zero _ (neg_ne_zero.2 (inv_ne_zero hq))) (det_map_unit hs (p2 g) Zh hZh).ne_zero

theorem inv_smul_q {n : Type} [Fintype n] [DecidableEq n] (c : F) (hc : c ≠ 0) (X : Matrix n n F)
    (hX : IsUnit X.det) : (c⁻¹ • X)⁻¹ = c • X⁻¹ := by
  apply Matrix.inv_eq_left_inv
  rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, mul_inv_cancel₀ hc, one_smul, Matrix.nonsing_inv_mul _ hX]

theorem inv_smul_qT {n : Type} [Fintype n] [DecidableEq n] (c : F) (hc : c ≠ 0) (X : Matrix n n F)
    (hX : IsUnit X.det) : (-c⁻¹ • X.transpose)⁻¹ = -c • (X⁻¹).transpose := by
  apply Matrix.inv_eq_left_inv
  rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, neg_mul_neg, mul_inv_cancel₀ hc, one_smul,
    ← Matrix.transpose_mul, Matrix.mul_nonsing_inv _ hX, Matrix.transpose_one]

theorem lastCoordinate_firstProj {Zh : Matrix (Fin (r + 1)) (Fin (r + 1)) E} (hZh : IsUnit Zh.det) (T T' : F)
    (l : Fin (r + 1) → M.R) :
    p1 g (laG (ZZm g Zh T T') l) = ∑ b, (g.q : F) * (Zh.map (p1 g))⁻¹ (Fin.last r) b * p1 g (l b) := by
  have hq := q_ne g
  simp only [laG, Matrix.mulVec, dotProduct, map_sum, map_mul]
  refine Finset.sum_congr rfl fun b _ => ?_
  have h := congrFun (congrFun (map_inv_of (p1 g) _ (zm_unit hs hZh T T')) (Fin.last r)) b
  rw [Matrix.map_apply] at h
  rw [h, zzMinus_firstProj hs, inv_smul_q hs _ hq _ (det_map_unit hs (p1 g) Zh hZh), Matrix.smul_apply, smul_eq_mul]

theorem lastCoordinate_secondProj {Zh : Matrix (Fin (r + 1)) (Fin (r + 1)) E} (hZh : IsUnit Zh.det) (T T' : F)
    (l : Fin (r + 1) → M.R) :
    p2 g (laG (ZZm g Zh T T') l) = ∑ b, -(g.q : F) * (Zh.map (p2 g))⁻¹ b (Fin.last r) * p2 g (l b) := by
  have hq := q_ne g
  simp only [laG, Matrix.mulVec, dotProduct, map_sum, map_mul]
  refine Finset.sum_congr rfl fun b _ => ?_
  have h := congrFun (congrFun (map_inv_of (p2 g) _ (zm_unit hs hZh T T')) (Fin.last r)) b
  rw [Matrix.map_apply] at h
  rw [h, zzMinus_secondProj hs, inv_smul_qT hs _ hq _ (det_map_unit hs (p2 g) Zh hZh), Matrix.smul_apply, smul_eq_mul,
    Matrix.transpose_apply]

theorem lambda_firstProj {Zh : Matrix (Fin (r + 1)) (Fin (r + 1)) E} (hZh : IsUnit Zh.det) (y : Fin (r + 1) → E) :
    p1 g (lamC Zh y) = ∑ b, (Zh.map (p1 g))⁻¹ (Fin.last r) b * p1 g (y b) := by
  simp only [lamC, Matrix.mulVec, dotProduct, map_sum, map_mul]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [← map_inv_of (p1 g) _ hZh, Matrix.map_apply]

theorem lambda_secondProj {Zh : Matrix (Fin (r + 1)) (Fin (r + 1)) E} (hZh : IsUnit Zh.det) (y : Fin (r + 1) → E) :
    p2 g (lamC Zh y) = ∑ b, (Zh.map (p2 g))⁻¹ (Fin.last r) b * p2 g (y b) := by
  simp only [lamC, Matrix.mulVec, dotProduct, map_sum, map_mul]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [← map_inv_of (p2 g) _ hZh, Matrix.map_apply]

theorem firstProj_conj_split (x : E) : p1 g ((M.L.cj : E →+* E) x) = p2 g x := by
  rw [adeleInfiniteComponent_apply, adele_ext_components, e_cjR]

theorem secondProj_conj_split (x : E) : p2 g ((M.L.cj : E →+* E) x) = p1 g x := by
  rw [adeleInfiniteComponent_apply, adele_ext_components, e_cjR]

theorem lambdaStar_firstProj {Zh : Matrix (Fin (r + 1)) (Fin (r + 1)) E} (hZh : IsUnit Zh.det) (y : Fin (r + 1) → E) :
    p1 g (lamStarC (M.L.cj : E →+* E) Zh y) = ∑ b, (Zh.map (p2 g))⁻¹ b (Fin.last r) * p1 g (y b) := by
  simp only [lamStarC, map_sum, map_mul, firstProj_conj_split hs]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [← map_inv_of (p2 g) _ hZh, Matrix.map_apply]

theorem lambdaStar_secondProj {Zh : Matrix (Fin (r + 1)) (Fin (r + 1)) E} (hZh : IsUnit Zh.det) (y : Fin (r + 1) → E) :
    p2 g (lamStarC (M.L.cj : E →+* E) Zh y) = ∑ b, (Zh.map (p1 g))⁻¹ b (Fin.last r) * p2 g (y b) := by
  simp only [lamStarC, map_sum, map_mul, secondProj_conj_split hs]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [← map_inv_of (p1 g) _ hZh, Matrix.map_apply]

theorem corner_inverse_firstProj {Zh : Matrix (Fin (r + 1)) (Fin (r + 1)) E} (hZh : IsUnit Zh.det) :
    p1 g (Zh⁻¹ (Fin.last r) (Fin.last r)) = (Zh.map (p1 g))⁻¹ (Fin.last r) (Fin.last r) := by
  rw [← map_inv_of (p1 g) _ hZh, Matrix.map_apply]

theorem corner_inverse_secondProj {Zh : Matrix (Fin (r + 1)) (Fin (r + 1)) E} (hZh : IsUnit Zh.det) :
    p2 g (Zh⁻¹ (Fin.last r) (Fin.last r)) = (Zh.map (p2 g))⁻¹ (Fin.last r) (Fin.last r) := by
  rw [← map_inv_of (p2 g) _ hZh, Matrix.map_apply]

end Formalism.L2.SG.LocalCountModules.AlgGSplit
