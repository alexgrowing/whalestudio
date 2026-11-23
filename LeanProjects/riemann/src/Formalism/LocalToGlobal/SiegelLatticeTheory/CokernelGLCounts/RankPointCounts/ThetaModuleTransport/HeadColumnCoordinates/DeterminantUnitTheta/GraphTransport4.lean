import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.DeterminantUnitTheta.CompOfMemR

noncomputable section

open ValuativeRel Formalism.MainNotions.S.Loc Formalism.L2.SG.LsDatumA Formalism.L2.SG.LocalCountModules.LocCntCommon

namespace Formalism.L2.SG.LocalCountModules.ThetaMbe0GWork

section Transport

theorem graph_transport4 {D₁ D₂ Dc₁ Dc₂ W₁ W₂ W₁' W₂' P P' : Type} (Ψ₁ : D₁ ≃ Dc₁) (Ψ₂ : D₂ ≃ Dc₂)
    (θ : D₁ ≃ D₂) (φ : W₁ → W₂) (φ' : W₁' → W₂') (Pc₁ : W₁ → P) (Pc₂ : W₂ → P) (Pc₁' : W₁' → P')
    (Pc₂' : W₂' → P') (Γ₁ : Set (D₁ × D₁ × W₁ × W₁')) (Γ₂ : Set (D₂ × D₂ × W₂ × W₂'))
    (Γc₁ : Set (Dc₁ × Dc₁ × P × P')) (Γc₂ : Set (Dc₂ × Dc₂ × P × P'))
    (h1 : (fun p => (Ψ₁ p.1, Ψ₁ p.2.1, Pc₁ p.2.2.1, Pc₁' p.2.2.2)) '' Γ₁ = Γc₁)
    (h2 : (fun p => (Ψ₂ p.1, Ψ₂ p.2.1, Pc₂ p.2.2.1, Pc₂' p.2.2.2)) '' Γ₂ = Γc₂)
    (hP : ∀ w, Pc₂ (φ w) = Pc₁ w) (hP' : ∀ w, Pc₂' (φ' w) = Pc₁' w)
    (hinj : ∀ p ∈ Γ₁, ∀ q ∈ Γ₂, Pc₂ q.2.2.1 = Pc₁ p.2.2.1 → Pc₂' q.2.2.2 = Pc₁' p.2.2.2 →
      q.2.2.1 = φ p.2.2.1 ∧ q.2.2.2 = φ' p.2.2.2) :
    ((fun p => (θ p.1, θ p.2.1, φ p.2.2.1, φ' p.2.2.2)) '' Γ₁ = Γ₂) ↔
      ((fun p => (Ψ₂ (θ (Ψ₁.symm p.1)), Ψ₂ (θ (Ψ₁.symm p.2.1)), p.2.2.1, p.2.2.2)) '' Γc₁ = Γc₂) := by
  subst h1 h2
  constructor
  · intro h
    rw [← h, Set.image_image, Set.image_image]
    congr 1
    funext p
    simp [hP, hP']
  · intro h
    ext q
    constructor
    · rintro ⟨p, hp, rfl⟩
      have hc : (Ψ₂ (θ p.1), Ψ₂ (θ p.2.1), Pc₁ p.2.2.1, Pc₁' p.2.2.2) ∈
          (fun p => (Ψ₂ p.1, Ψ₂ p.2.1, Pc₂ p.2.2.1, Pc₂' p.2.2.2)) '' Γ₂ := by
        rw [← h]
        exact ⟨_, ⟨p, hp, rfl⟩, by simp⟩
      obtain ⟨q, hq, hqe⟩ := hc
      simp only [Prod.mk.injEq] at hqe
      obtain ⟨e1, e2, e3, e4⟩ := hqe
      obtain ⟨f1, f2⟩ := hinj p hp q hq e3 e4
      have hpq : ((θ p.1, θ p.2.1, φ p.2.2.1, φ' p.2.2.2) : D₂ × D₂ × W₂ × W₂') = q :=
        Prod.ext (Ψ₂.injective e1).symm (Prod.ext (Ψ₂.injective e2).symm (Prod.ext f1.symm f2.symm))
      show ((θ p.1, θ p.2.1, φ p.2.2.1, φ' p.2.2.2) : D₂ × D₂ × W₂ × W₂') ∈ Γ₂
      rw [hpq]
      exact hq
    · intro hq
      have hc : (Ψ₂ q.1, Ψ₂ q.2.1, Pc₂ q.2.2.1, Pc₂' q.2.2.2) ∈
          (fun p => (Ψ₂ (θ (Ψ₁.symm p.1)), Ψ₂ (θ (Ψ₁.symm p.2.1)), p.2.2.1, p.2.2.2)) ''
            ((fun p => (Ψ₁ p.1, Ψ₁ p.2.1, Pc₁ p.2.2.1, Pc₁' p.2.2.2)) '' Γ₁) := by
        rw [h]
        exact ⟨q, hq, rfl⟩
      obtain ⟨_, ⟨p, hp, rfl⟩, hpe⟩ := hc
      simp only [Equiv.symm_apply_apply, Prod.mk.injEq] at hpe
      obtain ⟨e1, e2, e3, e4⟩ := hpe
      obtain ⟨f1, f2⟩ := hinj p hp q hq e3.symm e4.symm
      exact ⟨p, hp, Prod.ext (Ψ₂.injective e1) (Prod.ext (Ψ₂.injective e2) (Prod.ext f1.symm f2.symm))⟩

end Transport

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
variable {M : Model F E} {V : Type} [AddCommGroup V] [Module E V] (H : HermSp M V)
variable {r : ℕ}

def PcG {g : SplitG M.L} {t : Term V M r} (hg : GoodG H g t) : H.Wb t.f →ₗ[E] E × E :=
  coordW H t.f (t.f (Fin.last r)) (omP H t.f t.f') (z_mem H t.f t.T hg.2.1)
    (omP_mem H t.f t.f' hg.2.2.2.1)

def PcG' {g : SplitG M.L} {t : Term V M r} (hg : GoodG H g t) : H.Wb t.f' →ₗ[E] E × E :=
  coordW H t.f' (omP H t.f' t.f) (t.f' (Fin.last r))
    (omP_mem H t.f' t.f (unit_swap H t.f t.f' hg.2.2.2.1)) (z_mem H t.f' t.T' hg.2.2.1)

theorem pcG_mk {g : SplitG M.L} {t : Term V M r} (hg : GoodG H g t) (u : ↥(MMsharp H t))
    (hu : (u : V) ∈ H.perp (H.X t.f)) :
    PcG H hg (H.mkW t.f ⟨u, hu⟩) = ((sharpEquiv H t (unit_gramHG H hg) u (Sum.inl (Fin.last r)) : E),
      lamStarC (M.L.cj : E →+* E) (H.Zhat t.f t.f') (fun b =>
        (sharpEquiv H t (unit_gramHG H hg) u (Sum.inl b) : E) +
          algebraMap F E (g.q : F) * (sharpEquiv H t (unit_gramHG H hg) u (Sum.inr b) : E))) := by
  simp only [PcG, coordW_mk]
  refine Prod.ext ?_ ?_
  · show H.h u (t.f (Fin.last r)) = _
    rw [sharpG_inl H hg]
  · show H.h u (omP H t.f t.f') = _
    rw [h_omP, lamStarC]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [sharpG_f' H hg]
    rfl

theorem pcG'_mk {g : SplitG M.L} {t : Term V M r} (hg : GoodG H g t) (u : ↥(MMsharp H t))
    (hu : (u : V) ∈ H.perp (H.X t.f')) :
    PcG' H hg (H.mkW t.f' ⟨u, hu⟩) = (lamC (H.Zhat t.f t.f') (fun a =>
        (sharpEquiv H t (unit_gramHG H hg) u (Sum.inl a) : E)),
      (sharpEquiv H t (unit_gramHG H hg) u (Sum.inl (Fin.last r)) : E) +
        algebraMap F E (g.q : F) * (sharpEquiv H t (unit_gramHG H hg) u (Sum.inr (Fin.last r)) : E)) := by
  simp only [PcG', coordW_mk]
  refine Prod.ext ?_ ?_
  · show H.h u (omP H t.f' t.f) = _
    rw [h_omP_swap H t.f t.f' hg.2.2.2.1, lamC, Matrix.mulVec, dotProduct]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [sharpG_inl H hg]
  · show H.h u (t.f' (Fin.last r)) = _
    rw [sharpG_f' H hg]

theorem gamR_image {g : SplitG M.L} {t : Term V M r} (hg : GoodG H g t) :
    (fun p => (PsiG H hg p.1, PsiG H hg p.2.1, PcG H hg p.2.2.1, PcG' H hg p.2.2.2)) ''
        GamR H t (algebraMap F E (g.q : F)) =
      GamRC M.L.O (M.L.cj : E →+* E) (algebraMap F E (g.q : F)) (algebraMap F E ((g.q : F)⁻¹))
        (H.Zhat t.f t.f') (algebraMap F E t.T) (algebraMap F E t.T') := by
  set s := sharpEquiv H t (unit_gramHG H hg) with hsdef
  ext ⟨d, e, c, c'⟩
  constructor
  · rintro ⟨_, ⟨u, u', u'', hu, hu', huu, rfl⟩, he⟩
    refine ⟨s u, s u', s u'', fun a => ?_, fun a => ?_, fun i => ?_, ?_⟩
    · apply Subtype.ext
      rw [sharpG_inl H hg]
      exact (mem_perpX_iff H t.f u).1 hu a
    · rw [← sharpG_f' H hg]
      exact (mem_perpX_iff H t.f' u').1 hu' a
    · rw [sharpEquiv_apply, sharpEquiv_apply, sharpEquiv_apply, ← h_sub_left, huu, H.h_smul_left]
    · rw [← he]
      simp only [PsiG_mk, pcG_mk, pcG'_mk, ← hsdef]
  · rintro ⟨Y, Y', Y'', hY, hY', hYY, he⟩
    set u := s.symm Y with hu
    set u' := s.symm Y' with hu'
    set u'' := s.symm Y'' with hu''
    have sY : s u = Y := by rw [hu, LinearEquiv.apply_symm_apply]
    have sY' : s u' = Y' := by rw [hu', LinearEquiv.apply_symm_apply]
    have sY'' : s u'' = Y'' := by rw [hu'', LinearEquiv.apply_symm_apply]
    have hX : (u : V) ∈ H.perp (H.X t.f) := by
      rw [mem_perpX_iff]
      intro a
      rw [← sharpG_inl H hg, ← hsdef, sY, hY a]
      rfl
    have hX' : (u' : V) ∈ H.perp (H.X t.f') := by
      rw [mem_perpX_iff]
      intro a
      rw [sharpG_f' H hg, ← hsdef, sY']
      exact hY' a
    have hqO : algebraMap F E (g.q : F) ∈ M.L.O := Formalism.MainNotions.LocalModelPeriodLattices.algebraMap_mem_O M.L g.q
    have huu : (u : V) - u' = algebraMap F E (g.q : F) • (u'' : V) := by
      have h0 : u - u' - (⟨_, hqO⟩ : M.L.O) • u'' = 0 := by
        apply s.injective
        rw [map_zero, map_sub, map_sub, map_smul, sY, sY', sY'']
        funext i
        apply Subtype.ext
        simp only [Pi.sub_apply, Pi.smul_apply, Pi.zero_apply, smul_eq_mul]
        push_cast
        rw [hYY i]
        ring
      have h1 := congrArg Subtype.val h0
      simp only [Submodule.coe_sub, Submodule.coe_smul, Submodule.coe_zero, Subring.smul_def] at h1
      exact sub_eq_zero.1 h1
    refine ⟨(ddMk H t u, ddMk H t u'', H.mkW t.f ⟨u, hX⟩, H.mkW t.f' ⟨u', hX'⟩),
      ⟨u, u', u'', hX, hX', huu, rfl⟩, ?_⟩
    rw [he]
    simp only [PsiG_mk, pcG_mk, pcG'_mk, ← hsdef, sY, sY', sY'']

end Formalism.L2.SG.LocalCountModules.ThetaMbe0GWork
