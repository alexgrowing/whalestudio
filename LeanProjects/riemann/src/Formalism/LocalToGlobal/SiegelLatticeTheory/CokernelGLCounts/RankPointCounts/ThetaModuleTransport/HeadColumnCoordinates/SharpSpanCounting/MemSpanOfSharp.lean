import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.SharpSpanCounting.DlRSwapZero

noncomputable section

open ValuativeRel Formalism.MainNotions.S.Loc Formalism.L2.SG.LsDatumA

namespace Formalism.L2.SG.LocalCountModules.LocCntCommon

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
variable {M : Model F E} {V : Type} [AddCommGroup V] [Module E V] (H : HermSp M V)
variable {r : ℕ}

def PcL {t : Term V M r} (hg : GoodL H t) : H.Wb t.f →ₗ[E] E × E :=
  coordW H t.f (t.f (Fin.last r)) (omP H t.f t.f') (z_mem H t.f t.T hg.2.1)
    (omP_mem H t.f t.f' hg.2.2.2.1)

def PcL' {t : Term V M r} (hg : GoodL H t) : H.Wb t.f' →ₗ[E] E × E :=
  coordW H t.f' (omP H t.f' t.f) (t.f' (Fin.last r))
    (omP_mem H t.f' t.f (unit_swap H t.f t.f' hg.2.2.2.1)) (z_mem H t.f' t.T' hg.2.2.1)

theorem sharp_inl {t : Term V M r} (hg : GoodL H t) (u : ↥(MMsharp H t)) (a : Fin (r + 1)) :
    (sharpEquiv H t (unit_gramH H hg) u (Sum.inl a) : E) = H.h u (t.f a) := by
  show H.h u (H.MMfam t (Sum.inl a)) = H.h u (t.f a)
  simp only [HermSp.MMfam, hg.1, Sum.elim_inl]

theorem sharp_inr {t : Term V M r} (hg : GoodL H t) (u : ↥(MMsharp H t)) (b : Fin (r + 1)) :
    (sharpEquiv H t (unit_gramH H hg) u (Sum.inr b) : E) = H.h u (t.f' b) := by
  show H.h u (H.MMfam t (Sum.inr b)) = H.h u (t.f' b)
  simp only [HermSp.MMfam, hg.1, Sum.elim_inr]

theorem mem_span_of_sharp {t : Term V M r} (hg : GoodL H t) (u : ↥(MMsharp H t)) :
    (u : V) ∈ Submodule.span E (Set.range (Sum.elim t.f t.f')) := by
  have h := ((mem_MMsharp_iff H t u).1 u.2).1
  simp only [HermSp.MMfam, hg.1] at h
  exact h

theorem gam_image {t : Term V M r} (hg : GoodL H t) :
    (fun p => (Psi H hg p.1, PcL H hg p.2)) '' Gam H t =
      GamC M.L.O (M.L.cj : E →+* E) (H.Zhat t.f t.f') (algebraMap F E t.T) (algebraMap F E t.T') := by
  ext ⟨d, c⟩
  constructor
  · rintro ⟨_, ⟨u, hu, rfl⟩, he⟩
    refine ⟨sharpEquiv H t (unit_gramH H hg) u, fun a => ?_, ?_⟩
    · apply Subtype.ext
      rw [sharp_inl H hg]
      exact (mem_perpX_iff H t.f u).1 hu a
    · rw [← he]
      beta_reduce
      rw [Psi_mk]
      refine Prod.ext rfl (Prod.ext ?_ ?_)
      · show H.h u (t.f (Fin.last r)) = _
        rw [sharp_inl H hg]
      · show H.h u (omP H t.f t.f') = _
        rw [h_omP, lamStarC]
        refine Finset.sum_congr rfl fun b _ => ?_
        rw [sharp_inr H hg]
        rfl
  · rintro ⟨Y, hY, he⟩
    set u := (sharpEquiv H t (unit_gramH H hg)).symm Y with hu
    have hYu : sharpEquiv H t (unit_gramH H hg) u = Y := by rw [hu, LinearEquiv.apply_symm_apply]
    have hX : (u : V) ∈ H.perp (H.X t.f) := by
      rw [mem_perpX_iff]
      intro a
      rw [← sharp_inl H hg, hYu, hY a]
      rfl
    refine ⟨(ddMk H t u, H.mkW t.f ⟨u, hX⟩), ⟨u, hX, rfl⟩, ?_⟩
    rw [he]
    beta_reduce
    rw [Psi_mk, hYu]
    refine Prod.ext rfl (Prod.ext ?_ ?_)
    · show H.h u (t.f (Fin.last r)) = _
      rw [← sharp_inl H hg, hYu]
    · show H.h u (omP H t.f t.f') = _
      rw [h_omP, lamStarC]
      refine Finset.sum_congr rfl fun b _ => ?_
      rw [← sharp_inr H hg u, hYu]
      rfl

theorem gam_image' {t : Term V M r} (hg : GoodL H t) :
    (fun p => (Psi H hg p.1, PcL' H hg p.2)) '' Gam' H t =
      GamC' M.L.O (M.L.cj : E →+* E) (H.Zhat t.f t.f') (algebraMap F E t.T) (algebraMap F E t.T') := by
  ext ⟨d, c⟩
  constructor
  · rintro ⟨_, ⟨u, hu, rfl⟩, he⟩
    refine ⟨sharpEquiv H t (unit_gramH H hg) u, fun a => ?_, ?_⟩
    · apply Subtype.ext
      rw [sharp_inr H hg]
      exact (mem_perpX_iff H t.f' u).1 hu a
    · rw [← he]
      beta_reduce
      rw [Psi_mk]
      refine Prod.ext rfl (Prod.ext ?_ ?_)
      · show H.h u (omP H t.f' t.f) = _
        rw [h_omP_swap H t.f t.f' hg.2.2.2.1, lamC, Matrix.mulVec, dotProduct]
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [sharp_inl H hg]
      · show H.h u (t.f' (Fin.last r)) = _
        rw [sharp_inr H hg]
  · rintro ⟨Y, hY, he⟩
    set u := (sharpEquiv H t (unit_gramH H hg)).symm Y with hu
    have hYu : sharpEquiv H t (unit_gramH H hg) u = Y := by rw [hu, LinearEquiv.apply_symm_apply]
    have hX : (u : V) ∈ H.perp (H.X t.f') := by
      rw [mem_perpX_iff]
      intro a
      rw [← sharp_inr H hg, hYu, hY a]
      rfl
    refine ⟨(ddMk H t u, H.mkW t.f' ⟨u, hX⟩), ⟨u, hX, rfl⟩, ?_⟩
    rw [he]
    beta_reduce
    rw [Psi_mk, hYu]
    refine Prod.ext rfl (Prod.ext ?_ ?_)
    · show H.h u (omP H t.f' t.f) = _
      rw [h_omP_swap H t.f t.f' hg.2.2.2.1, lamC, Matrix.mulVec, dotProduct]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [← sharp_inl H hg u, hYu]
    · show H.h u (t.f' (Fin.last r)) = _
      rw [← sharp_inr H hg, hYu]

theorem gam_sep {t₁ t₂ : Term V M r} (hg₁ : GoodL H t₁) (hg₂ : GoodL H t₂) (hT : t₂.T = t₁.T)
    (φ : H.Wb t₁.f ≃ₗ[E] H.Wb t₂.f)
    (hz : φ (H.mkW t₁.f ⟨_, z_mem H t₁.f t₁.T hg₁.2.1⟩) = H.mkW t₂.f ⟨_, z_mem H t₂.f t₂.T hg₂.2.1⟩)
    (ho : φ (H.mkW t₁.f ⟨_, omP_mem H t₁.f t₁.f' hg₁.2.2.2.1⟩) =
      H.mkW t₂.f ⟨_, omP_mem H t₂.f t₂.f' hg₂.2.2.2.1⟩) :
    ∀ p ∈ Gam H t₁, ∀ q ∈ Gam H t₂, PcL H hg₂ q.2 = PcL H hg₁ p.2 → q.2 = φ p.2 := by
  rintro _ ⟨u₁, hu₁, rfl⟩ _ ⟨u₂, hu₂, rfl⟩ hc
  simp only [PcL, coordW_mk, Prod.mk.injEq] at hc
  show H.mkW t₂.f ⟨u₂, hu₂⟩ = φ (H.mkW t₁.f ⟨u₁, hu₁⟩)
  rw [mkW_decomp H t₂.f t₂.f' t₂.T t₂.T' hg₂.2.1 hg₂.2.2.1 hg₂.2.2.2.1 hg₂.2.2.2.2 ⟨u₂, hu₂⟩
      (mem_span_of_sharp H hg₂ u₂),
    mkW_decomp H t₁.f t₁.f' t₁.T t₁.T' hg₁.2.1 hg₁.2.2.1 hg₁.2.2.2.1 hg₁.2.2.2.2 ⟨u₁, hu₁⟩
      (mem_span_of_sharp H hg₁ u₁), map_add, map_smul, map_smul, hz, ho]
  have hT' : algebraMap F E t₂.T = algebraMap F E t₁.T := by rw [hT]
  simp only at hc ⊢
  rw [hc.1, hc.2, hT']

theorem gam_sep' {t₁ t₂ : Term V M r} (hg₁ : GoodL H t₁) (hg₂ : GoodL H t₂) (hT : t₂.T' = t₁.T')
    (φ' : H.Wb t₁.f' ≃ₗ[E] H.Wb t₂.f')
    (hz : φ' (H.mkW t₁.f' ⟨_, z_mem H t₁.f' t₁.T' hg₁.2.2.1⟩) =
      H.mkW t₂.f' ⟨_, z_mem H t₂.f' t₂.T' hg₂.2.2.1⟩)
    (ho : φ' (H.mkW t₁.f' ⟨_, omP_mem H t₁.f' t₁.f (unit_swap H t₁.f t₁.f' hg₁.2.2.2.1)⟩) =
      H.mkW t₂.f' ⟨_, omP_mem H t₂.f' t₂.f (unit_swap H t₂.f t₂.f' hg₂.2.2.2.1)⟩) :
    ∀ p ∈ Gam' H t₁, ∀ q ∈ Gam' H t₂, PcL' H hg₂ q.2 = PcL' H hg₁ p.2 → q.2 = φ' p.2 := by
  rintro _ ⟨u₁, hu₁, rfl⟩ _ ⟨u₂, hu₂, rfl⟩ hc
  simp only [PcL', coordW_mk, Prod.mk.injEq] at hc
  show H.mkW t₂.f' ⟨u₂, hu₂⟩ = φ' (H.mkW t₁.f' ⟨u₁, hu₁⟩)
  rw [mkW_decomp' H t₂.f t₂.f' t₂.T t₂.T' hg₂.2.1 hg₂.2.2.1 hg₂.2.2.2.1 hg₂.2.2.2.2 ⟨u₂, hu₂⟩
      (mem_span_of_sharp H hg₂ u₂),
    mkW_decomp' H t₁.f t₁.f' t₁.T t₁.T' hg₁.2.1 hg₁.2.2.1 hg₁.2.2.2.1 hg₁.2.2.2.2 ⟨u₁, hu₁⟩
      (mem_span_of_sharp H hg₁ u₁), map_add, map_smul, map_smul, hz, ho]
  have hT' : algebraMap F E t₂.T' = algebraMap F E t₁.T' := by rw [hT]
  simp only at hc ⊢
  rw [hc.1, hc.2, hT']

end Formalism.L2.SG.LocalCountModules.LocCntCommon
