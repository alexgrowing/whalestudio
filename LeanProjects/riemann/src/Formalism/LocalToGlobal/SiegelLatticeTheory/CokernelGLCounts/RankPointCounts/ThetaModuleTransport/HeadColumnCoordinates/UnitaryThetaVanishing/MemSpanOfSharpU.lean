import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.UnitaryThetaVanishing.HOmPOmPU

noncomputable section

open ValuativeRel Formalism.MainNotions.S.Loc Formalism.L2.SG.LsDatumA Formalism.L2.SG.LocalCountModules.LocCntCommon

namespace Formalism.L2.SG.LocalCountModules.UnitaryGroupMassFormula.ThetaMbeU

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
variable {M : Model F E} {V : Type} [AddCommGroup V] [Module E V] (H : HermSp M V)
variable {r : ℕ}

def nuU (f f' : Fin (r + 1) → V) : E := H.h (omP H f f') (omP H f f')

def alU (f f' : Fin (r + 1) → V) (T : F) (u : V) : E :=
  Ring.inverse (1 + algebraMap F E T * nuU H f f') * (H.h u (omP H f f') - nuU H f f' * H.h u (f (Fin.last r)))

theorem decompU (f f' : Fin (r + 1) → V) (T T' : F) (hF : Formalism.MainNotions.ThinScalesBound.FrameK H f T)
    (hF' : Formalism.MainNotions.ThinScalesBound.FrameK H f' T') (hD : IsUnit (H.Dl f f' (r + 1))) (hG : IsUnit (H.Gdet f f' T T'))
    (u : V) (hu : u ∈ Submodule.span E (Set.range (Sum.elim f f'))) (hX : u ∈ H.perp (H.X f)) :
    u - (alU H f f' T u • f (Fin.last r) + (H.h u (f (Fin.last r)) + algebraMap F E T * alU H f f' T u) •
      omP H f f') ∈ H.X f := by
  have hX' := (mem_perpX_iff H f u).1 hX
  apply mem_X_ofU H f f' T T' hF hF' hD hG
  · refine Submodule.sub_mem _ hu (Submodule.add_mem _ (Submodule.smul_mem _ _ ?_)
      (Submodule.smul_mem _ _ (omP_mem_span H f f')))
    exact Submodule.subset_span ⟨Sum.inl _, rfl⟩
  · intro a
    rw [h_sub_left H, H.h_add_left, H.h_smul_left, H.h_smul_left, h_frame H f T hF,
      h_omP_f H f f' hD]
    by_cases ha : a = Fin.last r
    · subst ha
      simp only [and_self, if_true]
      ring
    · obtain ⟨a', rfl⟩ := Fin.exists_castSucc_eq.2 ha
      simp [ha, hX' a']
  · have hη : (1 + algebraMap F E T * nuU H f f') * Ring.inverse (1 + algebraMap F E T * nuU H f f') = 1 :=
      Ring.mul_inverse_cancel _ (eta_unit H f f' T T' hF' hD hG)
    have e1 : H.h (u - (alU H f f' T u • f (Fin.last r) + (H.h u (f (Fin.last r)) +
        algebraMap F E T * alU H f f' T u) • omP H f f')) (omP H f f') = 0 := by
      rw [h_sub_left H, H.h_add_left, H.h_smul_left, H.h_smul_left, h_z_omP H f f' hD]
      rw [show H.h (omP H f f') (omP H f f') = nuU H f f' from rfl, alU]
      linear_combination (-(H.h u (omP H f f') - nuU H f f' * H.h u (f (Fin.last r)))) * hη
    have e2 : H.h (u - (alU H f f' T u • f (Fin.last r) + (H.h u (f (Fin.last r)) +
        algebraMap F E T * alU H f f' T u) • omP H f f')) (H.om' f f') = 0 := by
      rw [omP, h_smul_right] at e1
      have hu' : IsUnit (M.L.cj (Ring.inverse (H.Dl f f' (r + 1)))) :=
        (IsUnit.map M.L.cj (⟨⟨Ring.inverse (H.Dl f f' (r + 1)), H.Dl f f' (r + 1), Ring.inverse_mul_cancel _ hD,
          Ring.mul_inverse_cancel _ hD⟩, rfl⟩ :
          IsUnit (Ring.inverse (H.Dl f f' (r + 1)))))
      exact hu'.mul_right_eq_zero.1 e1
    rw [H.h_herm, e2, map_zero]

theorem mkW_decompU (f f' : Fin (r + 1) → V) (T T' : F) (hF : Formalism.MainNotions.ThinScalesBound.FrameK H f T)
    (hF' : Formalism.MainNotions.ThinScalesBound.FrameK H f' T') (hD : IsUnit (H.Dl f f' (r + 1))) (hG : IsUnit (H.Gdet f f' T T'))
    (u : ↥(H.perp (H.X f))) (hu : (u : V) ∈ Submodule.span E (Set.range (Sum.elim f f'))) :
    H.mkW f u = alU H f f' T u • H.mkW f ⟨f (Fin.last r), z_mem H f T hF⟩ +
      (H.h u (f (Fin.last r)) + algebraMap F E T * alU H f f' T u) •
        H.mkW f ⟨omP H f f', omP_mem H f f' hD⟩ := by
  have hd := decompU H f f' T T' hF hF' hD hG u hu u.2
  unfold HermSp.mkW
  rw [← map_smul, ← map_smul, ← map_add, Submodule.mkQ_apply, Submodule.mkQ_apply,
    Submodule.Quotient.eq, Submodule.mem_comap, Submodule.subtype_apply, Submodule.coe_sub,
    Submodule.coe_add, Submodule.coe_smul, Submodule.coe_smul]
  exact hd

theorem mkW_decompU' (f f' : Fin (r + 1) → V) (T T' : F) (hF : Formalism.MainNotions.ThinScalesBound.FrameK H f T)
    (hF' : Formalism.MainNotions.ThinScalesBound.FrameK H f' T') (hD : IsUnit (H.Dl f f' (r + 1))) (hG : IsUnit (H.Gdet f f' T T'))
    (u : ↥(H.perp (H.X f'))) (hu : (u : V) ∈ Submodule.span E (Set.range (Sum.elim f f'))) :
    H.mkW f' u = alU H f' f T' u • H.mkW f' ⟨f' (Fin.last r), z_mem H f' T' hF'⟩ +
      (H.h u (f' (Fin.last r)) + algebraMap F E T' * alU H f' f T' u) •
        H.mkW f' ⟨omP H f' f, omP_mem H f' f (unit_swap H f f' hD)⟩ := by
  have hG' : IsUnit (H.Gdet f' f T' T) := by
    have he : H.Gdet f' f T' T = H.Gdet f f' T T' := by
      unfold HermSp.Gdet HermSp.normE
      rw [dl_swap_full H f f', dl_swap_r H f f', M.L.cj_cj, M.L.cj_cj, mul_comm T' T]
      ring
    rw [he]
    exact hG
  have hu' : (u : V) ∈ Submodule.span E (Set.range (Sum.elim f' f)) := by
    rw [Set.Sum.elim_range, Set.union_comm, ← Set.Sum.elim_range]
    exact hu
  exact mkW_decompU H f' f T' T hF' hF (unit_swap H f f' hD) hG' u hu'

def GoodU {r : ℕ} (t : Term V M r) : Prop :=
  M.split = none ∧ Formalism.MainNotions.ThinScalesBound.FrameK H t.f t.T ∧ Formalism.MainNotions.ThinScalesBound.FrameK H t.f' t.T' ∧
    IsUnit (H.Dl t.f t.f' (r + 1)) ∧ IsUnit (H.Gdet t.f t.f' t.T t.T')

private theorem MMfam_eq_sum_elim_of_goodU {t : Term V M r} (hg : GoodU H t) : H.MMfam t = Sum.elim t.f t.f' := by
  unfold HermSp.MMfam
  rw [hg.1]

theorem gramH_eqU {r : ℕ} {t : Term V M r} (hg : GoodU H t) :
    gramH H (H.MMfam t) = gramC (M.L.cj : E →+* E) (H.Zhat t.f t.f') (algebraMap F E t.T)
      (algebraMap F E t.T') := by
  rw [MMfam_eq_sum_elim_of_goodU H hg]
  obtain ⟨-, ⟨h0, hT⟩, ⟨h0', hT'⟩, -, -⟩ := hg
  ext i j
  rcases i with a | a <;> rcases j with b | b <;>
    simp only [gramC, gramH, Matrix.of_apply, Sum.elim_inl, Sum.elim_inr, Matrix.fromBlocks_apply₁₁,
      Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂,
      Matrix.transpose_apply, HermSp.Zhat]
  · split_ifs with h
    · obtain ⟨rfl, rfl⟩ := h
      exact hT
    · exact h0 a b (not_and_or.mp h)
  · first
      | exact H.h_herm _ _
      | exact (H.h_herm _ _).symm
      | simp [H.h_herm]
  · split_ifs with h
    · obtain ⟨rfl, rfl⟩ := h
      exact hT'
    · exact h0' a b (not_and_or.mp h)

theorem unit_gramHU {r : ℕ} {t : Term V M r} (hg : GoodU H t) :
    IsUnit (gramH H (H.MMfam t)).det := by
  rw [gramH_eqU H hg]
  exact unit_gramC_of H t.f t.f' t.T t.T' hg.2.1 hg.2.2.1 hg.2.2.2.1 hg.2.2.2.2

theorem relSub_eqU {r : ℕ} {t : Term V M r} (hg : GoodU H t) :
    relSub H t = relC M.L.O (M.L.cj : E →+* E) (H.Zhat t.f t.f') (algebraMap F E t.T)
      (algebraMap F E t.T') := by
  ext y
  simp only [relSub, relC, Submodule.mem_mk, AddSubmonoid.mem_mk, AddSubsemigroup.mem_mk,
    Set.mem_setOf_eq]
  rw [← gramH_eqU H hg]
  rfl

def PsiU {r : ℕ} {t : Term V M r} (hg : GoodU H t) :
    DDt H t ≃ₗ[M.L.O] DDc M.L.O (M.L.cj : E →+* E) (H.Zhat t.f t.f') (algebraMap F E t.T)
      (algebraMap F E t.T') :=
  (ddEquiv H t (unit_gramHU H hg)).trans (Submodule.quotEquivOfEq _ _ (relSub_eqU H hg))

theorem PsiU_mk {r : ℕ} {t : Term V M r} (hg : GoodU H t) (u : ↥(MMsharp H t)) :
    PsiU H hg (ddMk H t u) = Submodule.Quotient.mk (sharpEquiv H t (unit_gramHU H hg) u) := rfl

theorem h_eq_formCU {r : ℕ} {t : Term V M r} (hg : GoodU H t) (u w : ↥(MMsharp H t)) :
    H.h u w = formC M.L.O (M.L.cj : E →+* E) (H.Zhat t.f t.f') (algebraMap F E t.T)
      (algebraMap F E t.T') (sharpEquiv H t (unit_gramHU H hg) u)
      (sharpEquiv H t (unit_gramHU H hg) w) := by
  rw [h_eq_form H (H.MMfam t) (unit_gramHU H hg) (u : V) (w : V) ((mem_MMsharp_iff H t u).1 u.2).1,
    gramH_eqU H hg]
  simp only [formC, sharpEquiv_apply]
  rfl

def PcU {t : Term V M r} (hg : GoodU H t) : H.Wb t.f →ₗ[E] E × E :=
  coordW H t.f (t.f (Fin.last r)) (omP H t.f t.f') (z_mem H t.f t.T hg.2.1)
    (omP_mem H t.f t.f' hg.2.2.2.1)

def PcU' {t : Term V M r} (hg : GoodU H t) : H.Wb t.f' →ₗ[E] E × E :=
  coordW H t.f' (omP H t.f' t.f) (t.f' (Fin.last r))
    (omP_mem H t.f' t.f (unit_swap H t.f t.f' hg.2.2.2.1)) (z_mem H t.f' t.T' hg.2.2.1)

theorem sharp_inlU {t : Term V M r} (hg : GoodU H t) (u : ↥(MMsharp H t)) (a : Fin (r + 1)) :
    (sharpEquiv H t (unit_gramHU H hg) u (Sum.inl a) : E) = H.h u (t.f a) := by
  rw [sharpEquiv_apply, MMfam_eq_sum_elim_of_goodU H hg, Sum.elim_inl]

theorem sharp_inrU {t : Term V M r} (hg : GoodU H t) (u : ↥(MMsharp H t)) (b : Fin (r + 1)) :
    (sharpEquiv H t (unit_gramHU H hg) u (Sum.inr b) : E) = H.h u (t.f' b) := by
  rw [sharpEquiv_apply, MMfam_eq_sum_elim_of_goodU H hg, Sum.elim_inr]

theorem mem_span_of_sharpU {t : Term V M r} (hg : GoodU H t) (u : ↥(MMsharp H t)) :
    (u : V) ∈ Submodule.span E (Set.range (Sum.elim t.f t.f')) := by
  have hs := ((mem_MMsharp_iff H t u).1 u.2).1
  rwa [MMfam_eq_sum_elim_of_goodU H hg] at hs

theorem gam_imageU {t : Term V M r} (hg : GoodU H t) :
    (fun p => (PsiU H hg p.1, PcU H hg p.2)) '' Gam H t =
      GamC M.L.O (M.L.cj : E →+* E) (H.Zhat t.f t.f') (algebraMap F E t.T) (algebraMap F E t.T') := by
  ext ⟨d, c⟩
  constructor
  · rintro ⟨_, ⟨u, hu, rfl⟩, he⟩
    refine ⟨sharpEquiv H t (unit_gramHU H hg) u, fun a => ?_, ?_⟩
    · apply Subtype.ext
      rw [sharp_inlU H hg]
      exact (mem_perpX_iff H t.f u).1 hu a
    · rw [← he]
      beta_reduce
      rw [PsiU_mk]
      refine Prod.ext rfl (Prod.ext ?_ ?_)
      · show H.h u (t.f (Fin.last r)) = _
        rw [sharp_inlU H hg]
      · show H.h u (omP H t.f t.f') = _
        rw [h_omP, lamStarC]
        refine Finset.sum_congr rfl fun b _ => ?_
        rw [sharp_inrU H hg]
        rfl
  · rintro ⟨Y, hY, he⟩
    set u := (sharpEquiv H t (unit_gramHU H hg)).symm Y with hu
    have hYu : sharpEquiv H t (unit_gramHU H hg) u = Y := by rw [hu, LinearEquiv.apply_symm_apply]
    have hX : (u : V) ∈ H.perp (H.X t.f) := by
      rw [mem_perpX_iff]
      intro a
      rw [← sharp_inlU H hg, hYu, hY a]
      rfl
    refine ⟨(ddMk H t u, H.mkW t.f ⟨u, hX⟩), ⟨u, hX, rfl⟩, ?_⟩
    rw [he]
    beta_reduce
    rw [PsiU_mk, hYu]
    refine Prod.ext rfl (Prod.ext ?_ ?_)
    · show H.h u (t.f (Fin.last r)) = _
      rw [← sharp_inlU H hg, hYu]
    · show H.h u (omP H t.f t.f') = _
      rw [h_omP, lamStarC]
      refine Finset.sum_congr rfl fun b _ => ?_
      rw [← sharp_inrU H hg u, hYu]
      rfl

theorem gam_imageU' {t : Term V M r} (hg : GoodU H t) :
    (fun p => (PsiU H hg p.1, PcU' H hg p.2)) '' Gam' H t =
      GamC' M.L.O (M.L.cj : E →+* E) (H.Zhat t.f t.f') (algebraMap F E t.T) (algebraMap F E t.T') := by
  ext ⟨d, c⟩
  constructor
  · rintro ⟨_, ⟨u, hu, rfl⟩, he⟩
    refine ⟨sharpEquiv H t (unit_gramHU H hg) u, fun a => ?_, ?_⟩
    · apply Subtype.ext
      rw [sharp_inrU H hg]
      exact (mem_perpX_iff H t.f' u).1 hu a
    · rw [← he]
      beta_reduce
      rw [PsiU_mk]
      refine Prod.ext rfl (Prod.ext ?_ ?_)
      · show H.h u (omP H t.f' t.f) = _
        rw [h_omP_swap H t.f t.f' hg.2.2.2.1, lamC, Matrix.mulVec, dotProduct]
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [sharp_inlU H hg]
      · show H.h u (t.f' (Fin.last r)) = _
        rw [sharp_inrU H hg]
  · rintro ⟨Y, hY, he⟩
    set u := (sharpEquiv H t (unit_gramHU H hg)).symm Y with hu
    have hYu : sharpEquiv H t (unit_gramHU H hg) u = Y := by rw [hu, LinearEquiv.apply_symm_apply]
    have hX : (u : V) ∈ H.perp (H.X t.f') := by
      rw [mem_perpX_iff]
      intro a
      rw [← sharp_inrU H hg, hYu, hY a]
      rfl
    refine ⟨(ddMk H t u, H.mkW t.f' ⟨u, hX⟩), ⟨u, hX, rfl⟩, ?_⟩
    rw [he]
    beta_reduce
    rw [PsiU_mk, hYu]
    refine Prod.ext rfl (Prod.ext ?_ ?_)
    · show H.h u (omP H t.f' t.f) = _
      rw [h_omP_swap H t.f t.f' hg.2.2.2.1, lamC, Matrix.mulVec, dotProduct]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [← sharp_inlU H hg u, hYu]
    · show H.h u (t.f' (Fin.last r)) = _
      rw [← sharp_inrU H hg, hYu]

theorem gam_sepU {t₁ t₂ : Term V M r} (hg₁ : GoodU H t₁) (hg₂ : GoodU H t₂) (hT : t₂.T = t₁.T)
    (hν : nuU H t₂.f t₂.f' = nuU H t₁.f t₁.f')
    (φ : H.Wb t₁.f ≃ₗ[E] H.Wb t₂.f)
    (hz : φ (H.mkW t₁.f ⟨_, z_mem H t₁.f t₁.T hg₁.2.1⟩) = H.mkW t₂.f ⟨_, z_mem H t₂.f t₂.T hg₂.2.1⟩)
    (ho : φ (H.mkW t₁.f ⟨_, omP_mem H t₁.f t₁.f' hg₁.2.2.2.1⟩) =
      H.mkW t₂.f ⟨_, omP_mem H t₂.f t₂.f' hg₂.2.2.2.1⟩) :
    ∀ p ∈ Gam H t₁, ∀ q ∈ Gam H t₂, PcU H hg₂ q.2 = PcU H hg₁ p.2 → q.2 = φ p.2 := by
  intro p hp q hq hc
  obtain ⟨u, hu, rfl⟩ := hp
  obtain ⟨w, hw, rfl⟩ := hq
  have e1 : H.h (w : V) (t₂.f (Fin.last r)) = H.h (u : V) (t₁.f (Fin.last r)) := congrArg Prod.fst hc
  have e2 : H.h (w : V) (omP H t₂.f t₂.f') = H.h (u : V) (omP H t₁.f t₁.f') := congrArg Prod.snd hc
  have hα : alU H t₂.f t₂.f' t₂.T (w : V) = alU H t₁.f t₁.f' t₁.T (u : V) := by
    unfold alU
    rw [hT, hν, e1, e2]
  have hβ : H.h (w : V) (t₂.f (Fin.last r)) + algebraMap F E t₂.T * alU H t₂.f t₂.f' t₂.T (w : V) =
      H.h (u : V) (t₁.f (Fin.last r)) + algebraMap F E t₁.T * alU H t₁.f t₁.f' t₁.T (u : V) := by
    rw [e1, hα, hT]
  show H.mkW t₂.f ⟨w, hw⟩ = φ (H.mkW t₁.f ⟨u, hu⟩)
  rw [mkW_decompU H t₂.f t₂.f' t₂.T t₂.T' hg₂.2.1 hg₂.2.2.1 hg₂.2.2.2.1 hg₂.2.2.2.2 ⟨w, hw⟩
      (mem_span_of_sharpU H hg₂ w),
    mkW_decompU H t₁.f t₁.f' t₁.T t₁.T' hg₁.2.1 hg₁.2.2.1 hg₁.2.2.2.1 hg₁.2.2.2.2 ⟨u, hu⟩
      (mem_span_of_sharpU H hg₁ u),
    map_add, map_smul, map_smul, hz, ho, hβ, hα]

theorem gam_sepU' {t₁ t₂ : Term V M r} (hg₁ : GoodU H t₁) (hg₂ : GoodU H t₂) (hT : t₂.T' = t₁.T')
    (hν : nuU H t₂.f' t₂.f = nuU H t₁.f' t₁.f)
    (φ' : H.Wb t₁.f' ≃ₗ[E] H.Wb t₂.f')
    (hz : φ' (H.mkW t₁.f' ⟨_, z_mem H t₁.f' t₁.T' hg₁.2.2.1⟩) =
      H.mkW t₂.f' ⟨_, z_mem H t₂.f' t₂.T' hg₂.2.2.1⟩)
    (ho : φ' (H.mkW t₁.f' ⟨_, omP_mem H t₁.f' t₁.f (unit_swap H t₁.f t₁.f' hg₁.2.2.2.1)⟩) =
      H.mkW t₂.f' ⟨_, omP_mem H t₂.f' t₂.f (unit_swap H t₂.f t₂.f' hg₂.2.2.2.1)⟩) :
    ∀ p ∈ Gam' H t₁, ∀ q ∈ Gam' H t₂, PcU' H hg₂ q.2 = PcU' H hg₁ p.2 → q.2 = φ' p.2 := by
  intro p hp q hq hc
  obtain ⟨u, hu, rfl⟩ := hp
  obtain ⟨w, hw, rfl⟩ := hq
  have e1 : H.h (w : V) (omP H t₂.f' t₂.f) = H.h (u : V) (omP H t₁.f' t₁.f) := congrArg Prod.fst hc
  have e2 : H.h (w : V) (t₂.f' (Fin.last r)) = H.h (u : V) (t₁.f' (Fin.last r)) := congrArg Prod.snd hc
  have hα : alU H t₂.f' t₂.f t₂.T' (w : V) = alU H t₁.f' t₁.f t₁.T' (u : V) := by
    unfold alU
    rw [hT, hν, e1, e2]
  have hβ : H.h (w : V) (t₂.f' (Fin.last r)) + algebraMap F E t₂.T' * alU H t₂.f' t₂.f t₂.T' (w : V) =
      H.h (u : V) (t₁.f' (Fin.last r)) + algebraMap F E t₁.T' * alU H t₁.f' t₁.f t₁.T' (u : V) := by
    rw [e2, hα, hT]
  show H.mkW t₂.f' ⟨w, hw⟩ = φ' (H.mkW t₁.f' ⟨u, hu⟩)
  rw [mkW_decompU' H t₂.f t₂.f' t₂.T t₂.T' hg₂.2.1 hg₂.2.2.1 hg₂.2.2.2.1 hg₂.2.2.2.2 ⟨w, hw⟩
      (mem_span_of_sharpU H hg₂ w),
    mkW_decompU' H t₁.f t₁.f' t₁.T t₁.T' hg₁.2.1 hg₁.2.2.1 hg₁.2.2.2.1 hg₁.2.2.2.2 ⟨u, hu⟩
      (mem_span_of_sharpU H hg₁ u),
    map_add, map_smul, map_smul, hz, ho, hβ, hα]

end Formalism.L2.SG.LocalCountModules.UnitaryGroupMassFormula.ThetaMbeU
