import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.SharpSpanCounting.OmPMemSpan

noncomputable section

open ValuativeRel Formalism.MainNotions.S.Loc Formalism.L2.SG.LsDatumA

namespace Formalism.L2.SG.LocalCountModules.LocCntCommon

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
variable {M : Model F E} {V : Type} [AddCommGroup V] [Module E V] (H : HermSp M V)
variable {r : ℕ}

theorem zhat_swap (f f' : Fin (r + 1) → V) :
    H.Zhat f' f = ((H.Zhat f f').transpose).map M.L.cj := by
  ext a b
  simp only [HermSp.Zhat, Matrix.of_apply, Matrix.map_apply, Matrix.transpose_apply]
  exact H.h_herm (f' a) (f b)

theorem dl_swap_full (f f' : Fin (r + 1) → V) :
    H.Dl f' f (r + 1) = M.L.cj (H.Dl f f' (r + 1)) := by
  unfold HermSp.Dl
  rw [dif_pos le_rfl, dif_pos le_rfl, zhat_swap, Matrix.submatrix_map, ← Matrix.transpose_submatrix,
    Matrix.transpose_map, Matrix.det_transpose]
  exact (RingHom.map_det (M.L.cj : E →+* E) _).symm

theorem dl_swap_r (f f' : Fin (r + 1) → V) :
    H.Dl f' f r = M.L.cj (H.Dl f f' r) := by
  unfold HermSp.Dl
  rw [dif_pos (Nat.le_succ r), dif_pos (Nat.le_succ r), zhat_swap, Matrix.submatrix_map,
    ← Matrix.transpose_submatrix, Matrix.transpose_map, Matrix.det_transpose]
  exact (RingHom.map_det (M.L.cj : E →+* E) _).symm

theorem om_swap (f f' : Fin (r + 1) → V) : H.om' f' f = H.om f f' := by
  unfold HermSp.om' HermSp.om
  rw [zhat_swap]
  refine Finset.sum_congr rfl fun b _ => ?_
  congr 1
  rw [Matrix.transpose_map, ← Matrix.adjugate_transpose, Matrix.transpose_apply]
  exact congrFun (congrFun (RingHom.map_adjugate (M.L.cj : E →+* E) (H.Zhat f f')).symm _) _

theorem inv_swap (f f' : Fin (r + 1) → V) (hD : IsUnit (H.Dl f f' (r + 1))) (a b : Fin (r + 1)) :
    (H.Zhat f' f)⁻¹ a b = M.L.cj ((H.Zhat f f')⁻¹ b a) := by
  have hdet : IsUnit (H.Zhat f f').det := by
    have e : H.Dl f f' (r + 1) = (H.Zhat f f').det := by
      unfold HermSp.Dl
      rw [dif_pos le_rfl]
      rfl
    rw [← e]
    exact hD
  have key : H.Zhat f' f * (((H.Zhat f f')⁻¹).transpose).map M.L.cj = 1 := by
    rw [zhat_swap]
    have e2 : ((H.Zhat f f').transpose).map M.L.cj * (((H.Zhat f f')⁻¹).transpose).map M.L.cj =
        (((H.Zhat f f')⁻¹ * H.Zhat f f').transpose).map M.L.cj := by
      rw [Matrix.transpose_mul]
      exact (Matrix.map_mul (f := (M.L.cj : E →+* E))).symm
    rw [e2, Matrix.nonsing_inv_mul _ hdet, Matrix.transpose_one, Matrix.map_one _ (map_zero _) (map_one _)]
  rw [Matrix.inv_eq_right_inv key]
  rfl

theorem span_swap (f f' : Fin (r + 1) → V) :
    Submodule.span E (Set.range (Sum.elim f' f)) = Submodule.span E (Set.range (Sum.elim f f')) := by
  rw [Set.Sum.elim_range, Set.Sum.elim_range, Set.union_comm]

theorem h_omP_swap (f f' : Fin (r + 1) → V) (hD : IsUnit (H.Dl f f' (r + 1))) (u : V) :
    H.h u (omP H f' f) = ∑ a, (H.Zhat f f')⁻¹ (Fin.last r) a * H.h u (f a) := by
  have hDl' : H.Dl f' f (r + 1) = (H.Zhat f' f).det := by
    unfold HermSp.Dl
    rw [dif_pos le_rfl]
    rfl
  have e1 : omP H f' f = ∑ b, (H.Zhat f' f)⁻¹ b (Fin.last r) • f b := by
    unfold omP HermSp.om'
    rw [Finset.smul_sum, hDl', Matrix.inv_def]
    simp only [smul_smul, Matrix.smul_apply, smul_eq_mul]
  rw [e1, H.h_herm, h_sum_left, map_sum]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [map_mul, ← H.h_herm, inv_swap H f f' hD, M.L.cj_cj]

theorem unit_swap (f f' : Fin (r + 1) → V) (hD : IsUnit (H.Dl f f' (r + 1))) :
    IsUnit (H.Dl f' f (r + 1)) := by
  rw [dl_swap_full]
  exact hD.map (M.L.cj : E →+* E)

theorem dl_r_swap_zero (f f' : Fin (r + 1) → V) (hD0 : H.Dl f f' r = 0) : H.Dl f' f r = 0 := by
  rw [dl_swap_r, hD0, map_zero]

theorem mkW_decomp' (f f' : Fin (r + 1) → V) (T T' : F) (hF : Formalism.MainNotions.ThinScalesBound.FrameK H f T)
    (hF' : Formalism.MainNotions.ThinScalesBound.FrameK H f' T') (hD : IsUnit (H.Dl f f' (r + 1))) (hD0 : H.Dl f f' r = 0)
    (u : ↥(H.perp (H.X f'))) (hu : (u : V) ∈ Submodule.span E (Set.range (Sum.elim f f'))) :
    H.mkW f' u = H.h u (omP H f' f) • H.mkW f' ⟨f' (Fin.last r), z_mem H f' T' hF'⟩ +
      (H.h u (f' (Fin.last r)) + algebraMap F E T' * H.h u (omP H f' f)) •
        H.mkW f' ⟨omP H f' f, omP_mem H f' f (unit_swap H f f' hD)⟩ :=
  mkW_decomp H f' f T' T hF' hF (unit_swap H f f' hD) (dl_r_swap_zero H f f' hD0) u
    (by rw [span_swap]; exact hu)

theorem sends_omP' {f₁ f₁' f₂ f₂' : Fin (r + 1) → V} (φ' : H.Wb f₁' ≃ₗ[E] H.Wb f₂')
    (hD₁ : IsUnit (H.Dl f₁ f₁' (r + 1))) (hD₂ : IsUnit (H.Dl f₂ f₂' (r + 1)))
    (hs : H.SendsTo φ'.toLinearMap (M.L.cj (H.Dl f₂ f₂' (r + 1))) (M.L.cj (H.Dl f₁ f₁' (r + 1)))
      (H.om f₁ f₁') (H.om f₂ f₂')) :
    φ' (H.mkW f₁' ⟨omP H f₁' f₁, omP_mem H f₁' f₁ (unit_swap H f₁ f₁' hD₁)⟩) =
      H.mkW f₂' ⟨omP H f₂' f₂, omP_mem H f₂' f₂ (unit_swap H f₂ f₂' hD₂)⟩ := by
  have hs' : H.SendsTo φ'.toLinearMap (H.Dl f₂' f₂ (r + 1)) (H.Dl f₁' f₁ (r + 1)) (H.om' f₁' f₁)
      (H.om' f₂' f₂) := by
    rw [dl_swap_full H f₂ f₂', dl_swap_full H f₁ f₁', om_swap H f₁ f₁', om_swap H f₂ f₂']
    exact hs
  exact sends_omP H φ' (unit_swap H f₁ f₁' hD₁) (unit_swap H f₂ f₂' hD₂) hs'

end Formalism.L2.SG.LocalCountModules.LocCntCommon
