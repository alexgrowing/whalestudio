import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.ThinScalesBound
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.LsDatumA

noncomputable section

open ValuativeRel Matrix

namespace Formalism.L2.SG.LsDatumA

open Formalism.MainNotions.S.Loc

section Gram

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
variable {M : Model F E} {V : Type} [AddCommGroup V] [Module E V] (H : HermSp M V)

def hL (y : V) : V →ₗ[E] E where
  toFun x := H.h x y
  map_add' x x' := H.h_add_left x x' y
  map_smul' a x := H.h_smul_left a x y

theorem h_sum_smul_left {ι : Type} [Fintype ι] (c : ι → E) (v : ι → V) (y : V) :
    H.h (∑ i, c i • v i) y = ∑ i, c i * H.h (v i) y := by
  show hL H y (∑ i, c i • v i) = _
  rw [map_sum]
  simp only [map_smul, smul_eq_mul]
  rfl

theorem h_sub_left (x x' y : V) : H.h (x - x') y = H.h x y - H.h x' y := (hL H y).map_sub x x'

theorem h_sum_smul_right {ι : Type} [Fintype ι] (c : ι → E) (v : ι → V) (w : V) :
    H.h w (∑ i, c i • v i) = ∑ i, M.L.cj (c i) * H.h w (v i) := by
  rw [H.h_herm (∑ i, c i • v i) w, h_sum_smul_left, map_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [map_mul, H.h_herm (v i) w]

theorem isCompl_span_perp {ι : Type} [Fintype ι] [DecidableEq ι] (v : ι → V) (hG : IsUnit (H.gram v).det) :
    IsCompl (Submodule.span E (Set.range v)) (H.perp (Submodule.span E (Set.range v))) := by
  have hmv : ∀ (c : ι → E) (j : ι), H.h (∑ i, c i • v i) (v j) = (H.gram v *ᵥ c) j := by
    intro c j
    rw [h_sum_smul_left]
    show _ = ∑ i, H.gram v j i * c i
    simp only [HermSp.gram, Matrix.of_apply]
    exact Finset.sum_congr rfl (fun i _ => mul_comm _ _)
  constructor
  · rw [Submodule.disjoint_def]
    intro x hx hxp
    obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun E).1 hx
    have hc : H.gram v *ᵥ c = 0 := by
      funext j
      rw [← hmv]
      exact hxp (v j) (Submodule.subset_span ⟨j, rfl⟩)
    have hc0 : c = 0 := by
      have := congrArg (fun w => (H.gram v)⁻¹ *ᵥ w) hc
      simpa [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hG] using this
    subst hc0
    simp
  · rw [codisjoint_iff, eq_top_iff]
    rintro x -
    set c := (H.gram v)⁻¹ *ᵥ (fun j => H.h x (v j)) with hc
    have hsum : ∑ i, c i • v i ∈ Submodule.span E (Set.range v) :=
      (Submodule.mem_span_range_iff_exists_fun E).2 ⟨c, rfl⟩
    have hperp : x - ∑ i, c i • v i ∈ H.perp (Submodule.span E (Set.range v)) := by
      intro y hy
      obtain ⟨d, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun E).1 hy
      rw [h_sum_smul_right]
      refine Finset.sum_eq_zero (fun j _ => ?_)
      rw [h_sub_left, hmv, hc, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hG, Matrix.one_mulVec]
      simp
    exact Submodule.mem_sup.2 ⟨_, hsum, _, hperp, by abel⟩

variable {r : ℕ}

def cornerM (c : E) : Matrix (Fin (r + 1)) (Fin (r + 1)) E :=
  Matrix.of fun a b => if a = Fin.last r ∧ b = Fin.last r then c else 0

theorem cornerM_mul (c : E) (N : Matrix (Fin (r + 1)) (Fin (r + 1)) E) (a k : Fin (r + 1)) :
    (cornerM (r := r) c * N) a k = if a = Fin.last r then c * N (Fin.last r) k else 0 := by
  simp only [cornerM, Matrix.mul_apply, Matrix.of_apply]
  split_ifs with ha
  · subst ha
    simp
  · simp [ha]

theorem mul_cornerM (c : E) (N : Matrix (Fin (r + 1)) (Fin (r + 1)) E) (k b : Fin (r + 1)) :
    (N * cornerM (r := r) c) k b = if b = Fin.last r then N k (Fin.last r) * c else 0 := by
  simp only [cornerM, Matrix.mul_apply, Matrix.of_apply]
  split_ifs with hb
  · subst hb
    simp
  · simp [hb]

theorem gram_eq_fromBlocks (f f' : Fin (r + 1) → V) (T T' : F) (hF : Formalism.MainNotions.ThinScalesBound.FrameK H f T)
    (hF' : Formalism.MainNotions.ThinScalesBound.FrameK H f' T') :
    H.gram (Sum.elim f f') = fromBlocks (cornerM (-algebraMap F E T)) (H.Zhat f f')
      (Matrix.of fun a b => M.L.cj (H.Zhat f f' b a)) (cornerM (-algebraMap F E T')) := by
  ext i j
  rcases i with a | a <;> rcases j with b | b
  · simp only [HermSp.gram, Matrix.of_apply, Sum.elim_inl, Matrix.fromBlocks_apply₁₁, cornerM]
    split_ifs with h
    · obtain ⟨rfl, rfl⟩ := h
      exact hF.2
    · exact hF.1 b a (not_and_or.1 h).symm
  · simp only [HermSp.gram, HermSp.Zhat, Matrix.of_apply, Sum.elim_inl, Sum.elim_inr, Matrix.fromBlocks_apply₁₂]
  · simp only [HermSp.gram, HermSp.Zhat, Matrix.of_apply, Sum.elim_inl, Sum.elim_inr, Matrix.fromBlocks_apply₂₁]
    exact H.h_herm (f' a) (f b)
  · simp only [HermSp.gram, Matrix.of_apply, Sum.elim_inr, Matrix.fromBlocks_apply₂₂, cornerM]
    split_ifs with h
    · obtain ⟨rfl, rfl⟩ := h
      exact hF'.2
    · exact hF'.1 b a (not_and_or.1 h).symm

private theorem det_sub_cornerM (N : Matrix (Fin (r + 1)) (Fin (r + 1)) E) (t : E) :
    (N - cornerM t).det = N.det - t * (N.submatrix Fin.castSucc Fin.castSucc).det := by
  have hP : (-1 : E) ^ ((Fin.last r : ℕ) + (Fin.last r : ℕ)) = 1 := by
    rw [← two_mul, pow_mul]
    simp
  have hsub : ∀ j : Fin (r + 1), (N - cornerM t).submatrix (Fin.last r).succAbove j.succAbove =
      N.submatrix (Fin.last r).succAbove j.succAbove := by
    intro j
    ext a b
    simp only [Matrix.submatrix_apply, Matrix.sub_apply, cornerM, Matrix.of_apply, Fin.succAbove_last]
    rw [if_neg (fun h => (Fin.castSucc_lt_last a).ne h.1), sub_zero]
  have hrow : ∀ k : Fin r, (N - cornerM t : Matrix (Fin (r + 1)) (Fin (r + 1)) E) (Fin.last r) k.castSucc =
      N (Fin.last r) k.castSucc := by
    intro k
    simp only [Matrix.sub_apply, cornerM, Matrix.of_apply]
    rw [if_neg (fun h => (Fin.castSucc_lt_last k).ne h.2), sub_zero]
  rw [Matrix.det_succ_row (N - cornerM t) (Fin.last r), Matrix.det_succ_row N (Fin.last r),
    Fin.sum_univ_castSucc, Fin.sum_univ_castSucc]
  simp only [hsub, hrow, hP]
  simp only [Matrix.sub_apply, cornerM, Matrix.of_apply, eq_self_iff_true, and_self, ite_true,
    Fin.succAbove_last]
  ring

private theorem det_cj_transpose_eq_cj_det {n : Type} [Fintype n] [DecidableEq n] (N : Matrix n n E) :
    (Matrix.of fun a b => M.L.cj (N b a)).det = M.L.cj N.det := by
  calc (Matrix.of fun a b => M.L.cj (N b a)).det
      = ((M.L.cj : E →+* E).mapMatrix N).transpose.det := rfl
    _ = ((M.L.cj : E →+* E).mapMatrix N).det := Matrix.det_transpose _
    _ = (M.L.cj : E →+* E) N.det := (RingHom.map_det _ _).symm
    _ = M.L.cj N.det := rfl

theorem gram_det (f f' : Fin (r + 1) → V) (T T' : F) (hF : Formalism.MainNotions.ThinScalesBound.FrameK H f T)
    (hF' : Formalism.MainNotions.ThinScalesBound.FrameK H f' T') (hD : IsUnit (H.Dl f f' (r + 1))) :
    ∃ s : E, s * s = 1 ∧ (H.gram (Sum.elim f f')).det * s = H.Gdet f f' T T' := by
  classical
  have hdB : H.Dl f f' (r + 1) = (H.Zhat f f').det := by
    rw [HermSp.Dl, dif_pos le_rfl]
    exact congrArg Matrix.det (Matrix.ext fun i j => rfl)
  have hdBr : H.Dl f f' r = ((H.Zhat f f').submatrix Fin.castSucc Fin.castSucc).det := by
    rw [HermSp.Dl, dif_pos (by omega : r ≤ r + 1)]
    exact congrArg Matrix.det (Matrix.ext fun i j => rfl)
  haveI hBinv : Invertible (H.Zhat f f') := Matrix.invertibleOfIsUnitDet _ (hdB ▸ hD)
  have hcorner : cornerM (r := r) (-algebraMap F E T') * ⅟(H.Zhat f f') * cornerM (-algebraMap F E T) =
      cornerM (algebraMap F E T * algebraMap F E T' * (⅟(H.Zhat f f')) (Fin.last r) (Fin.last r)) := by
    ext a b
    rw [mul_cornerM, cornerM_mul]
    simp only [cornerM, Matrix.of_apply]
    by_cases ha : a = Fin.last r <;> by_cases hb : b = Fin.last r <;> simp [ha, hb] <;> ring
  have hP : (-1 : E) ^ ((Fin.last r : ℕ) + (Fin.last r : ℕ)) = 1 := by
    rw [← two_mul, pow_mul]
    simp
  have hinv : (⅟(H.Zhat f f')) (Fin.last r) (Fin.last r) =
      Ring.inverse (H.Zhat f f').det * ((H.Zhat f f').submatrix Fin.castSucc Fin.castSucc).det := by
    rw [Matrix.invOf_eq_nonsing_inv, Matrix.inv_def, Matrix.smul_apply,
      Matrix.adjugate_fin_succ_eq_det_submatrix, Fin.succAbove_last, smul_eq_mul, hP, one_mul]
  have hC : (Matrix.of fun a b => M.L.cj (H.Zhat f f' b a)).det = M.L.cj (H.Zhat f f').det :=
    det_cj_transpose_eq_cj_det _
  have hCs : ((Matrix.of fun a b => M.L.cj (H.Zhat f f' b a)).submatrix Fin.castSucc Fin.castSucc).det =
      M.L.cj ((H.Zhat f f').submatrix Fin.castSucc Fin.castSucc).det :=
    det_cj_transpose_eq_cj_det _
  have hu : (H.Zhat f f').det * Ring.inverse (H.Zhat f f').det = 1 :=
    Ring.mul_inverse_cancel _ (hdB ▸ hD)
  rw [gram_eq_fromBlocks H f f' T T' hF hF']
  refine ⟨((Equiv.Perm.sign (Equiv.sumComm (Fin (r + 1)) (Fin (r + 1))) : ℤ) : E), ?_, ?_⟩
  · rw [← Int.cast_mul, ← Units.val_mul, Int.units_mul_self, Units.val_one, Int.cast_one]
  · have h1 := Matrix.det_permute' (Equiv.sumComm (Fin (r + 1)) (Fin (r + 1)))
      (Matrix.fromBlocks (cornerM (-algebraMap F E T)) (H.Zhat f f')
        (Matrix.of fun a b => M.L.cj (H.Zhat f f' b a)) (cornerM (-algebraMap F E T')))
    have hperm : (Matrix.fromBlocks (cornerM (-algebraMap F E T)) (H.Zhat f f')
        (Matrix.of fun a b => M.L.cj (H.Zhat f f' b a)) (cornerM (-algebraMap F E T'))).submatrix id
          (Equiv.sumComm (Fin (r + 1)) (Fin (r + 1))) =
        Matrix.fromBlocks (H.Zhat f f') (cornerM (-algebraMap F E T)) (cornerM (-algebraMap F E T'))
          (Matrix.of fun a b => M.L.cj (H.Zhat f f' b a)) := by
      ext (i | i) (j | j) <;> rfl
    rw [hperm, Matrix.det_fromBlocks₁₁, hcorner, det_sub_cornerM, hinv, hC, hCs] at h1
    simp only [HermSp.Gdet, HermSp.normE]
    rw [hdB, hdBr, (algebraMap F E).map_mul T T']
    linear_combination (-1 : E) * h1 - (algebraMap F E T * algebraMap F E T' *
      (((H.Zhat f f').submatrix Fin.castSucc Fin.castSucc).det *
        M.L.cj ((H.Zhat f f').submatrix Fin.castSucc Fin.castSucc).det)) * hu

theorem isUnit_Gdet (f f' : Fin (r + 1) → V) (T T' : F) (hG : H.Gdet f f' T T' ≠ 0) :
    IsUnit (H.Gdet f f' T T') := by
  have hfix : M.L.cj (H.Gdet f f' T T') = H.Gdet f f' T T' := by
    simp only [HermSp.Gdet, HermSp.normE, map_sub, map_mul, AlgEquiv.commutes, M.L.cj_cj] <;> ring
  obtain ⟨a, ha⟩ := (M.L.cj_fix _).1 hfix
  rw [← ha] at hG ⊢
  have ha0 : a ≠ 0 := by
    rintro rfl
    exact hG (map_zero _)
  exact (IsUnit.mk0 a ha0).map (algebraMap F E)

theorem isCompl_span_frames_W0 (f f' : Fin (r + 1) → V) (T T' : F) (hF : Formalism.MainNotions.ThinScalesBound.FrameK H f T)
    (hF' : Formalism.MainNotions.ThinScalesBound.FrameK H f' T') (hD : IsUnit (H.Dl f f' (r + 1))) (hG : IsUnit (H.Gdet f f' T T')) :
    IsCompl (Submodule.span E (Set.range (Sum.elim f f'))) (H.W0 f f') := by
  have hsp : H.Xp f ⊔ H.Xp f' = Submodule.span E (Set.range (Sum.elim f f')) := by
    simp only [HermSp.Xp, Set.Sum.elim_range, Submodule.span_union]
  obtain ⟨s, hs, hdet⟩ := gram_det H f f' T T' hF hF' hD
  have hu : IsUnit (H.gram (Sum.elim f f')).det := by
    have h' := hG
    rw [← hdet] at h'
    exact isUnit_of_mul_isUnit_left h'
  have hW : H.W0 f f' = H.perp (Submodule.span E (Set.range (Sum.elim f f'))) := by
    rw [← hsp]
    rfl
  rw [hW]
  exact isCompl_span_perp H _ hu

end Gram

end Formalism.L2.SG.LsDatumA
