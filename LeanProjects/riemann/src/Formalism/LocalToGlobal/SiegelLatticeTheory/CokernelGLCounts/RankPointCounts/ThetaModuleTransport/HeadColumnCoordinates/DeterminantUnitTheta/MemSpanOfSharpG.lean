import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.DeterminantUnitTheta.DetAddCor
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.SharpSpanCounting.CoordLHolds

noncomputable section

open ValuativeRel Formalism.MainNotions.S.Loc Formalism.L2.SG.LsDatumA Formalism.L2.SG.LocalCountModules.LocCntCommon

namespace Formalism.L2.SG.LocalCountModules.ThetaMbe0GWork

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
variable {M : Model F E} {V : Type} [AddCommGroup V] [Module E V] (H : HermSp M V)
variable {r : ℕ}

def GoodG (g : SplitG M.L) (t : Term V M r) : Prop :=
  M.split = some g ∧ Formalism.MainNotions.ThinScalesBound.FrameK H t.f t.T ∧ Formalism.MainNotions.ThinScalesBound.FrameK H t.f' t.T' ∧
    IsUnit (H.Dl t.f t.f' (r + 1)) ∧ IsUnit (gramH H (H.MMfam t)).det

theorem q_ne (g : SplitG M.L) : (g.q : F) ≠ 0 := by
  intro h
  exact g.q_irr.ne_zero (by exact_mod_cast h)

theorem qi_mul_q (g : SplitG M.L) :
    algebraMap F E ((g.q : F)⁻¹) * algebraMap F E (g.q : F) = 1 := by
  rw [← map_mul, inv_mul_cancel₀ (q_ne g), map_one]

theorem cj_alg (a : F) : M.L.cj (algebraMap F E a) = algebraMap F E a := M.L.cj.commutes a

theorem mmfam_some {g : SplitG M.L} (hs : M.split = some g) (t : Term V M r) :
    H.MMfam t = Sum.elim t.f (fun a => algebraMap F E ((g.q : F)⁻¹) • (t.f' a - t.f a)) := by
  simp only [HermSp.MMfam, hs]

theorem h_sub_right (x y y' : V) : H.h x (y - y') = H.h x y - H.h x y' := by
  have h1 : H.h (y - y') x = H.h y x - H.h y' x := by
    have h2 := H.h_add_left (y - y') y' x
    rw [sub_add_cancel] at h2
    rw [h2]
    ring
  rw [H.h_herm (y - y') x, h1, map_sub, ← H.h_herm, ← H.h_herm]

theorem gramH_eqG {g : SplitG M.L} {t : Term V M r} (hg : GoodG H g t) :
    gramH H (H.MMfam t) = gramG (M.L.cj : E →+* E) (algebraMap F E ((g.q : F)⁻¹)) (H.Zhat t.f t.f')
      (algebraMap F E t.T) (algebraMap F E t.T') := by
  obtain ⟨hs, hF, hF', -, -⟩ := hg
  have hff : ∀ a b, H.h (t.f a) (t.f b) = cor r a b (-algebraMap F E t.T) := by
    intro a b
    unfold cor
    split_ifs with h
    · rw [h.1, h.2]
      exact hF.2
    · exact hF.1 a b (by tauto)
  have hf'f' : ∀ a b, H.h (t.f' a) (t.f' b) = cor r a b (-algebraMap F E t.T') := by
    intro a b
    unfold cor
    split_ifs with h
    · rw [h.1, h.2]
      exact hF'.2
    · exact hF'.1 a b (by tauto)
  have hZ : ∀ a b, H.Zhat t.f t.f' a b = H.h (t.f' b) (t.f a) := fun a b => rfl
  have hZc : ∀ a b, (M.L.cj : E →+* E) (H.Zhat t.f t.f' a b) = H.h (t.f a) (t.f' b) := fun a b => by
    show M.L.cj (H.Zhat t.f t.f' a b) = _
    rw [hZ, ← H.h_herm]
  have hsr : ∀ (c : E) (x y : V), H.h x (c • y) = M.L.cj c * H.h x y := fun c x y => by
    rw [H.h_herm, H.h_smul_left, map_mul, ← H.h_herm]
  have hsl : ∀ (x y z : V), H.h (x - y) z = H.h x z - H.h y z := fun x y z => by
    have h2 := H.h_add_left (x - y) y z
    rw [sub_add_cancel] at h2
    rw [h2]
    ring
  rw [mmfam_some H hs]
  ext i j
  rcases i with a | a <;> rcases j with b | b
  · simp only [gramH, Matrix.of_apply, Sum.elim_inl, gramG, Matrix.fromBlocks_apply₁₁]
    exact hff a b
  · simp only [gramH, Matrix.of_apply, Sum.elim_inl, Sum.elim_inr, gramG, Matrix.fromBlocks_apply₁₂]
    rw [hsr, cj_alg, h_sub_right, hff, hZc]
    unfold cor
    split_ifs <;> ring
  · simp only [gramH, Matrix.of_apply, Sum.elim_inl, Sum.elim_inr, gramG, Matrix.fromBlocks_apply₂₁]
    rw [H.h_smul_left, hsl, hff, hZ]
    unfold cor
    split_ifs <;> ring
  · simp only [gramH, Matrix.of_apply, Sum.elim_inr, gramG, Matrix.fromBlocks_apply₂₂]
    rw [H.h_smul_left, hsr, cj_alg, hsl, h_sub_right, h_sub_right, hf'f', hff, hZc, hZ]
    unfold cor
    split_ifs <;> ring

theorem gramH_comb {ι : Type} [Fintype ι] (B : Matrix ι ι E) (v : ι → V) :
    gramH H (fun i => ∑ j, B i j • v j) = B * gramH H v * (B.map M.L.cj).transpose := by
  classical
  have hsl : ∀ (s : Finset ι) (f : ι → V) (y : V), H.h (∑ i ∈ s, f i) y = ∑ i ∈ s, H.h (f i) y := by
    intro s f y
    induction s using Finset.induction_on with
    | empty =>
      have h0 := H.h_smul_left 0 0 y
      simpa using h0
    | @insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, H.h_add_left, ih]
  have hsr : ∀ (x : V) (s : Finset ι) (f : ι → V), H.h x (∑ i ∈ s, f i) = ∑ i ∈ s, H.h x (f i) := by
    intro x s f
    rw [H.h_herm (∑ i ∈ s, f i) x, hsl, map_sum]
    simp_rw [← H.h_herm]
  have hsmr : ∀ (a : E) (x y : V), H.h x (a • y) = M.L.cj a * H.h x y := by
    intro a x y
    rw [H.h_herm (a • y) x, H.h_smul_left, map_mul, ← H.h_herm]
  ext i k
  simp only [gramH, Matrix.of_apply, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, hsl, H.h_smul_left,
    hsr, hsmr, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl (fun j _ => Finset.sum_congr rfl (fun l _ => by ring))

theorem unit_gramH_of {g : SplitG M.L} (hs : M.split = some g) {t : Term V M r}
    (hF : Formalism.MainNotions.ThinScalesBound.FrameK H t.f t.T) (hF' : Formalism.MainNotions.ThinScalesBound.FrameK H t.f' t.T')
    (hD1 : IsUnit (H.Dl t.f t.f' (r + 1))) (hD0 : H.Dl t.f t.f' r = 0) :
    IsUnit (gramH H (H.MMfam t)).det := by
  set qi := algebraMap F E ((g.q : F)⁻¹) with hqi
  let B : Matrix (Ix r) (Ix r) E := Matrix.fromBlocks 1 0 (-qi • (1 : Matrix (Fin (r + 1)) (Fin (r + 1)) E))
    (qi • (1 : Matrix (Fin (r + 1)) (Fin (r + 1)) E))
  have hfam : H.MMfam t = fun i => ∑ j, B i j • Sum.elim t.f t.f' j := by
    rw [mmfam_some H hs]
    funext i
    rcases i with a | a
    · simp [B, Fintype.sum_sum_type, Matrix.one_apply]
    · simp [B, Fintype.sum_sum_type, Matrix.one_apply, sub_eq_add_neg, add_comm, neg_smul]
      rfl
  have hqu : IsUnit qi := by
    refine ⟨⟨qi, algebraMap F E (g.q : F), qi_mul_q g, ?_⟩, rfl⟩
    rw [mul_comm]; exact qi_mul_q g
  have hB : IsUnit B.det := by
    simp only [B]
    rw [Matrix.det_fromBlocks_zero₁₂, Matrix.det_one, one_mul, Matrix.det_smul, Matrix.det_one, mul_one]
    exact hqu.pow _
  have hV : gramH H (Sum.elim t.f t.f') = gramC (M.L.cj : E →+* E) (H.Zhat t.f t.f')
      (algebraMap F E t.T) (algebraMap F E t.T') := by
    rw [gramC_eq H _ _ _ _ hF hF']
    ext i j; rfl
  have hG := unit_gramC H _ _ _ _ hF hF' hD1 hD0
  rw [hfam, gramH_comb, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, hV]
  have hBc : IsUnit (B.map M.L.cj).det := by
    have : (B.map M.L.cj).det = M.L.cj B.det := by
      rw [show (B.map M.L.cj) = (M.L.cj : E →+* E).mapMatrix B from rfl, ← RingHom.map_det]; rfl
    rw [this]; exact hB.map _
  exact (hB.mul hG).mul hBc

theorem unit_gramHG {g : SplitG M.L} {t : Term V M r} (hg : GoodG H g t) :
    IsUnit (gramH H (H.MMfam t)).det := hg.2.2.2.2

theorem relSub_eqG {g : SplitG M.L} {t : Term V M r} (hg : GoodG H g t) :
    relSub H t = relG M.L.O (M.L.cj : E →+* E) (algebraMap F E ((g.q : F)⁻¹)) (H.Zhat t.f t.f')
      (algebraMap F E t.T) (algebraMap F E t.T') := by
  have e : ∀ i j, H.h (H.MMfam t i) (H.MMfam t j) = gramG (M.L.cj : E →+* E) (algebraMap F E ((g.q : F)⁻¹))
      (H.Zhat t.f t.f') (algebraMap F E t.T) (algebraMap F E t.T') i j := by
    intro i j
    rw [← gramH_eqG H hg]
    rfl
  ext y
  constructor
  · rintro ⟨c, hc⟩
    exact ⟨c, fun j => by rw [hc j]; simp only [e]⟩
  · rintro ⟨c, hc⟩
    exact ⟨c, fun j => by rw [hc j]; simp only [e]⟩

def PsiG {g : SplitG M.L} {t : Term V M r} (hg : GoodG H g t) :
    DDt H t ≃ₗ[M.L.O] DDg M.L.O (M.L.cj : E →+* E) (algebraMap F E ((g.q : F)⁻¹)) (H.Zhat t.f t.f')
      (algebraMap F E t.T) (algebraMap F E t.T') :=
  (ddEquiv H t (unit_gramHG H hg)).trans (Submodule.quotEquivOfEq _ _ (relSub_eqG H hg))

theorem PsiG_mk {g : SplitG M.L} {t : Term V M r} (hg : GoodG H g t) (u : ↥(MMsharp H t)) :
    PsiG H hg (ddMk H t u) = Submodule.Quotient.mk (sharpEquiv H t (unit_gramHG H hg) u) := rfl

theorem PsiG_symm_mk {g : SplitG M.L} {t : Term V M r} (hg : GoodG H g t) (Y : Ix r → M.L.O) :
    (PsiG H hg).symm (Submodule.Quotient.mk Y) =
      ddMk H t ((sharpEquiv H t (unit_gramHG H hg)).symm Y) := by
  rw [LinearEquiv.symm_apply_eq, PsiG_mk, LinearEquiv.apply_symm_apply]

theorem h_eq_formG {g : SplitG M.L} {t : Term V M r} (hg : GoodG H g t) (u w : ↥(MMsharp H t)) :
    H.h u w = formG M.L.O (M.L.cj : E →+* E) (algebraMap F E ((g.q : F)⁻¹)) (H.Zhat t.f t.f')
      (algebraMap F E t.T) (algebraMap F E t.T') (sharpEquiv H t (unit_gramHG H hg) u)
      (sharpEquiv H t (unit_gramHG H hg) w) := by
  rw [h_eq_form H (H.MMfam t) (unit_gramHG H hg) u w ((mem_MMsharp_iff H t u).1 u.2).1]
  unfold formG
  rw [← gramH_eqG H hg]
  simp only [sharpEquiv_apply]
  rfl

theorem sharpG_inl {g : SplitG M.L} {t : Term V M r} (hg : GoodG H g t) (u : ↥(MMsharp H t))
    (a : Fin (r + 1)) : (sharpEquiv H t (unit_gramHG H hg) u (Sum.inl a) : E) = H.h u (t.f a) := by
  rw [sharpEquiv_apply, mmfam_some H hg.1]
  rfl

theorem sharpG_inr {g : SplitG M.L} {t : Term V M r} (hg : GoodG H g t) (u : ↥(MMsharp H t))
    (a : Fin (r + 1)) : (sharpEquiv H t (unit_gramHG H hg) u (Sum.inr a) : E) =
      algebraMap F E ((g.q : F)⁻¹) * (H.h u (t.f' a) - H.h u (t.f a)) := by
  rw [sharpEquiv_apply, mmfam_some H hg.1]
  simp only [Sum.elim_inr]
  rw [H.h_herm, H.h_smul_left, map_mul, ← H.h_herm, cj_alg, h_sub_right]

theorem sharpG_f' {g : SplitG M.L} {t : Term V M r} (hg : GoodG H g t) (u : ↥(MMsharp H t))
    (a : Fin (r + 1)) : H.h u (t.f' a) = (sharpEquiv H t (unit_gramHG H hg) u (Sum.inl a) : E) +
      algebraMap F E (g.q : F) * (sharpEquiv H t (unit_gramHG H hg) u (Sum.inr a) : E) := by
  rw [sharpG_inl H hg, sharpG_inr H hg, ← mul_assoc, mul_comm (algebraMap F E (g.q : F)), qi_mul_q g, one_mul]
  ring

theorem mem_span_of_sharpG {g : SplitG M.L} {t : Term V M r} (hg : GoodG H g t) (u : ↥(MMsharp H t)) :
    (u : V) ∈ Submodule.span E (Set.range (Sum.elim t.f t.f')) := by
  have h1 := ((mem_MMsharp_iff H t u).1 u.2).1
  rw [mmfam_some H hg.1] at h1
  refine Submodule.span_le.2 ?_ h1
  rintro _ ⟨i, rfl⟩
  rcases i with a | a
  · exact Submodule.subset_span ⟨Sum.inl a, rfl⟩
  · simp only [Sum.elim_inr]
    exact Submodule.smul_mem _ _ (Submodule.sub_mem _ (Submodule.subset_span ⟨Sum.inr a, rfl⟩)
      (Submodule.subset_span ⟨Sum.inl a, rfl⟩))

end Formalism.L2.SG.LocalCountModules.ThetaMbe0GWork
