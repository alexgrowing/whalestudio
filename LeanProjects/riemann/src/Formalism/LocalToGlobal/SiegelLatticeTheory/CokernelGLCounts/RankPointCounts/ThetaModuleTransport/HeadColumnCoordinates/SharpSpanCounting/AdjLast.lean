import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.SharpSpanCounting.GraphTransport

noncomputable section

open ValuativeRel Formalism.MainNotions.S.Loc Formalism.L2.SG.LsDatumA

namespace Formalism.L2.SG.LocalCountModules.LocCntCommon

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
variable {M : Model F E} {V : Type} [AddCommGroup V] [Module E V] (H : HermSp M V)
variable {r : ℕ}

theorem h_frame (f : Fin (r + 1) → V) (T : F) (hF : Formalism.MainNotions.ThinScalesBound.FrameK H f T) (a b : Fin (r + 1)) :
    H.h (f b) (f a) = if a = Fin.last r ∧ b = Fin.last r then -algebraMap F E T else 0 := by
  split_ifs with hab
  · obtain ⟨rfl, rfl⟩ := hab
    exact hF.2
  · apply hF.1 b a
    by_contra hc
    push_neg at hc
    exact hab ⟨hc.2, hc.1⟩

theorem adj_last (f f' : Fin (r + 1) → V) :
    (H.Zhat f f').adjugate (Fin.last r) (Fin.last r) = H.Dl f f' r := by
  rw [Matrix.adjugate_fin_succ_eq_det_submatrix]
  unfold HermSp.Dl
  rw [dif_pos (Nat.le_succ r)]
  have hpow : ((-1 : E) ^ ((Fin.last r : ℕ) + (Fin.last r : ℕ))) = 1 := by
    rw [Fin.val_last, ← two_mul, pow_mul]
    simp
  rw [hpow, one_mul]
  congr 1
  ext i j
  simp [Matrix.submatrix_apply, Fin.succAbove_last]
  rfl

theorem h_om'_f' (f f' : Fin (r + 1) → V) (T' : F) (hF' : Formalism.MainNotions.ThinScalesBound.FrameK H f' T')
    (hD0 : H.Dl f f' r = 0) (b : Fin (r + 1)) : H.h (H.om' f f') (f' b) = 0 := by
  unfold HermSp.om'
  rw [h_sum_left]
  apply Finset.sum_eq_zero
  intro c _
  by_cases hc : c = Fin.last r ∧ b = Fin.last r
  · obtain ⟨rfl, rfl⟩ := hc
    rw [adj_last, hD0, zero_mul]
  · rw [hF'.1 c b (not_and_or.mp hc), mul_zero]

theorem mem_X_of (f f' : Fin (r + 1) → V) (T T' : F) (hF : Formalism.MainNotions.ThinScalesBound.FrameK H f T)
    (hF' : Formalism.MainNotions.ThinScalesBound.FrameK H f' T') (hD : IsUnit (H.Dl f f' (r + 1))) (hD0 : H.Dl f f' r = 0)
    (v : V) (hv : v ∈ Submodule.span E (Set.range (Sum.elim f f')))
    (h1 : ∀ a, H.h v (f a) = 0) (h2 : H.h (H.om' f f') v = 0) : v ∈ H.X f := by
  obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun E).1 hv
  rw [Fintype.sum_sum_type] at h1 h2 ⊢
  simp only [Sum.elim_inl, Sum.elim_inr] at h1 h2 ⊢

  have hl : c (Sum.inl (Fin.last r)) = 0 := by
    rw [h_add_right, h_sum_right, h_sum_right] at h2
    simp only [h_om'_f' H f f' T' hF' hD0, mul_zero, Finset.sum_const_zero, add_zero, h_om'_f] at h2
    rw [Finset.sum_eq_single (Fin.last r) (fun b _ hb => by rw [if_neg hb, mul_zero])
      (by simp), if_pos rfl, ← dl_full] at h2
    have h3 : M.L.cj (c (Sum.inl (Fin.last r))) = 0 := (hD.mul_left_eq_zero).1 h2
    have := congrArg M.L.cj h3
    rwa [M.L.cj_cj, map_zero] at this

  have hZ : (H.Zhat f f').mulVec (fun b => c (Sum.inr b)) = 0 := by
    funext a
    have := h1 a
    rw [H.h_add_left, h_sum_left, h_sum_left] at this
    simp only [h_frame H f T hF] at this
    rw [Finset.sum_eq_single (Fin.last r) (fun b _ hb => by simp [hb]) (by simp)] at this
    simp only [hl, zero_mul, zero_add] at this
    rw [Pi.zero_apply, Matrix.mulVec, dotProduct, ← this]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [mul_comm]; rfl
  have hp' : (fun b => c (Sum.inr b)) = 0 := by
    have hu : IsUnit (H.Zhat f f').det := by rw [← dl_full]; exact hD
    have := congrArg (fun w => (H.Zhat f f')⁻¹.mulVec w) hZ
    simpa [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hu] using this
  have hp'' : ∀ b, c (Sum.inr b) = 0 := fun b => congrFun hp' b
  simp only [hp'', zero_smul, Finset.sum_const_zero, add_zero]
  rw [Fin.sum_univ_castSucc, hl, zero_smul, add_zero]
  exact Submodule.sum_mem _ fun a _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, rfl⟩)

end Formalism.L2.SG.LocalCountModules.LocCntCommon
