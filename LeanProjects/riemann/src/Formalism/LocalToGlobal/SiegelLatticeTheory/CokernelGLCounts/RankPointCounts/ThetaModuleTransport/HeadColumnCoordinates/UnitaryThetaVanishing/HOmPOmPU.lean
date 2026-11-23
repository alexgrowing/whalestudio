import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.SharpSpanCounting.CoordLHolds
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.UnitaryThetaVanishing.ThetaMbeUFalseOf

noncomputable section

open ValuativeRel Formalism.MainNotions.S.Loc Formalism.L2.SG.LsDatumA Formalism.L2.SG.LocalCountModules.LocCntCommon

namespace Formalism.L2.SG.LocalCountModules.UnitaryGroupMassFormula.ThetaMbeU

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
variable {M : Model F E} {V : Type} [AddCommGroup V] [Module E V] (H : HermSp M V)
variable {r : ℕ}

def kapU (f f' : Fin (r + 1) → V) : E := Ring.inverse (H.Dl f f' (r + 1)) * H.Dl f f' r

theorem h_om'_f'U (f f' : Fin (r + 1) → V) (T' : F) (hF' : Formalism.MainNotions.ThinScalesBound.FrameK H f' T') (b : Fin (r + 1)) :
    H.h (H.om' f f') (f' b) = if b = Fin.last r then H.Dl f f' r * -algebraMap F E T' else 0 := by
  unfold HermSp.om'
  rw [h_sum_smul_left]
  by_cases hb : b = Fin.last r
  · subst hb
    rw [if_pos rfl, Finset.sum_eq_single (Fin.last r)]
    · rw [hF'.2, adj_last]
    · intro c _ hc
      rw [hF'.1 c (Fin.last r) (Or.inl hc), mul_zero]
    · simp
  · rw [if_neg hb]
    apply Finset.sum_eq_zero
    intro c _
    rw [hF'.1 c b (Or.inr hb), mul_zero]

theorem h_om'_om'U (f f' : Fin (r + 1) → V) (T' : F) (hF' : Formalism.MainNotions.ThinScalesBound.FrameK H f' T') :
    H.h (H.om' f f') (H.om' f f') = M.L.cj (H.Dl f f' r) * (H.Dl f f' r * -algebraMap F E T') := by
  have e := h_sum_smul_left (H := H) (fun c => (H.Zhat f f').adjugate c (Fin.last r)) f' (H.om' f f')
  change H.h (∑ c, (H.Zhat f f').adjugate c (Fin.last r) • f' c) (H.om' f f') = _
  rw [e, Finset.sum_eq_single (Fin.last r)]
  · rw [H.h_herm, h_om'_f'U H f f' T' hF', if_pos rfl, adj_last, map_mul, map_neg, AlgEquiv.commutes]
    ring
  · intro c _ hc
    rw [H.h_herm, h_om'_f'U H f f' T' hF', if_neg hc, map_zero, mul_zero]
  · simp

private theorem hermSp_h_smul_right_eq_cj_mul' (x y : V) (a : E) : H.h x (a • y) = M.L.cj a * H.h x y := by
  rw [H.h_herm, H.h_smul_left, map_mul, ← H.h_herm]

theorem h_omP_omPU (f f' : Fin (r + 1) → V) (T' : F) (hF' : Formalism.MainNotions.ThinScalesBound.FrameK H f' T') :
    H.h (omP H f f') (omP H f f') = -(algebraMap F E T') * (kapU H f f' * M.L.cj (kapU H f f')) := by
  unfold omP kapU
  rw [H.h_smul_left, hermSp_h_smul_right_eq_cj_mul', h_om'_om'U H f f' T' hF', map_mul]
  ring

theorem eta_mul (f f' : Fin (r + 1) → V) (T T' : F) (hF' : Formalism.MainNotions.ThinScalesBound.FrameK H f' T')
    (hD : IsUnit (H.Dl f f' (r + 1))) :
    (1 + algebraMap F E T * H.h (omP H f f') (omP H f f')) * H.normE (H.Dl f f' (r + 1)) =
      H.Gdet f f' T T' := by
  rw [h_omP_omPU H f f' T' hF']
  unfold kapU HermSp.Gdet HermSp.normE
  have hinv : Ring.inverse (H.Dl f f' (r + 1)) * H.Dl f f' (r + 1) = 1 := Ring.inverse_mul_cancel _ hD
  have hinv' : M.L.cj (Ring.inverse (H.Dl f f' (r + 1))) * M.L.cj (H.Dl f f' (r + 1)) = 1 := by
    rw [← map_mul, hinv, map_one]
  rw [map_mul, map_mul (algebraMap F E)]
  linear_combination (-(algebraMap F E T) * algebraMap F E T' * H.Dl f f' r * M.L.cj (H.Dl f f' r) *
      M.L.cj (Ring.inverse (H.Dl f f' (r + 1))) * M.L.cj (H.Dl f f' (r + 1))) * hinv +
    (-(algebraMap F E T) * algebraMap F E T' * H.Dl f f' r * M.L.cj (H.Dl f f' r)) * hinv'

theorem eta_unit (f f' : Fin (r + 1) → V) (T T' : F) (hF' : Formalism.MainNotions.ThinScalesBound.FrameK H f' T')
    (hD : IsUnit (H.Dl f f' (r + 1))) (hG : IsUnit (H.Gdet f f' T T')) :
    IsUnit (1 + algebraMap F E T * H.h (omP H f f') (omP H f f')) :=
  isUnit_of_mul_isUnit_left (by rw [eta_mul H f f' T T' hF' hD]; exact hG)

theorem mem_X_ofU (f f' : Fin (r + 1) → V) (T T' : F) (hF : Formalism.MainNotions.ThinScalesBound.FrameK H f T)
    (hF' : Formalism.MainNotions.ThinScalesBound.FrameK H f' T') (hD : IsUnit (H.Dl f f' (r + 1))) (hG : IsUnit (H.Gdet f f' T T'))
    (v : V) (hv : v ∈ Submodule.span E (Set.range (Sum.elim f f')))
    (h1 : ∀ a, H.h v (f a) = 0) (h2 : H.h (H.om' f f') v = 0) : v ∈ H.X f := by
  obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun E).1 hv
  rw [Fintype.sum_sum_type] at h1 h2 ⊢
  simp only [Sum.elim_inl, Sum.elim_inr] at h1 h2 ⊢
  have hu : IsUnit (H.Zhat f f').det := by rw [← dl_full]; exact hD
  have hZ : (H.Zhat f f').mulVec (fun b => c (Sum.inr b)) =
      Pi.single (Fin.last r) (algebraMap F E T * c (Sum.inl (Fin.last r))) := by
    funext a
    have := h1 a
    rw [H.h_add_left, h_sum_left, h_sum_left] at this
    simp only [h_frame H f T hF] at this
    rw [Finset.sum_eq_single (Fin.last r) (fun b _ hb => by simp [hb]) (by simp)] at this
    have e : (H.Zhat f f').mulVec (fun b => c (Sum.inr b)) a = ∑ b, c (Sum.inr b) * H.h (f' b) (f a) := by
      rw [Matrix.mulVec, dotProduct]
      exact Finset.sum_congr rfl fun b _ => mul_comm _ _
    rw [e]
    by_cases ha : a = Fin.last r
    · subst ha
      simp only [and_self, if_true] at this
      rw [Pi.single_eq_same]
      linear_combination this
    · simp only [ha, false_and, if_false, mul_zero, zero_add] at this
      rw [Pi.single_eq_of_ne ha]
      exact this
  have hc'eq : (fun b => c (Sum.inr b)) =
      (H.Zhat f f')⁻¹.mulVec (Pi.single (Fin.last r) (algebraMap F E T * c (Sum.inl (Fin.last r)))) := by
    rw [← hZ, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hu, Matrix.one_mulVec]
  have hcl' : c (Sum.inr (Fin.last r)) = kapU H f f' * (algebraMap F E T * c (Sum.inl (Fin.last r))) := by
    have := congrFun hc'eq (Fin.last r)
    have hs : Pi.single (Fin.last r) (algebraMap F E T * c (Sum.inl (Fin.last r))) =
        (algebraMap F E T * c (Sum.inl (Fin.last r))) • Pi.single (Fin.last r) (1 : E) := by
      ext i
      by_cases hi : i = Fin.last r <;> simp [hi]
    rw [hs, Matrix.mulVec_smul, Matrix.mulVec_single_one, Pi.smul_apply, Matrix.col_apply, smul_eq_mul,
      Matrix.inv_def, Matrix.smul_apply, smul_eq_mul, adj_last, ← dl_full] at this
    rw [kapU]
    exact this.trans (by ring)
  have hl : c (Sum.inl (Fin.last r)) = 0 := by
    rw [h_add_right, h_sum_right, h_sum_right] at h2
    simp only [h_om'_f, h_om'_f'U H f f' T' hF'] at h2
    rw [Finset.sum_eq_single (Fin.last r) (fun b _ hb => by rw [if_neg hb, mul_zero]) (by simp),
      Finset.sum_eq_single (Fin.last r) (fun b _ hb => by rw [if_neg hb, mul_zero]) (by simp),
      if_pos rfl, if_pos rfl, ← dl_full, hcl', kapU, map_mul, map_mul, map_mul, AlgEquiv.commutes] at h2
    have h3 : M.L.cj (H.Dl f f' (r + 1)) * M.L.cj (Ring.inverse (H.Dl f f' (r + 1))) = 1 := by
      rw [← map_mul, Ring.mul_inverse_cancel _ hD, map_one]
    have hmul : M.L.cj (c (Sum.inl (Fin.last r))) * H.Gdet f f' T T' = 0 := by
      unfold HermSp.Gdet HermSp.normE
      rw [(algebraMap F E).map_mul]
      linear_combination (M.L.cj (H.Dl f f' (r + 1))) * h2 +
        (algebraMap F E T * algebraMap F E T' * H.Dl f f' r * M.L.cj (H.Dl f f' r) *
          M.L.cj (c (Sum.inl (Fin.last r)))) * h3
    have h4 := hG.mul_left_eq_zero.1 hmul
    have := congrArg M.L.cj h4
    rwa [M.L.cj_cj, map_zero] at this
  have hp'' : ∀ b, c (Sum.inr b) = 0 := by
    intro b
    have := congrFun hc'eq b
    rw [hl, mul_zero, Pi.single_zero, Matrix.mulVec_zero] at this
    exact this
  simp only [hp'', zero_smul, Finset.sum_const_zero, add_zero]
  rw [Fin.sum_univ_castSucc, hl, zero_smul, add_zero]
  exact Submodule.sum_mem _ fun a _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, rfl⟩)

end Formalism.L2.SG.LocalCountModules.UnitaryGroupMassFormula.ThetaMbeU
