import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.RgFwdSub
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.RgFwdSup
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.RgBwdSub
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.RgBwdSup
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.SharpDualSpans.GlueConvPf

noncomputable section

open ValuativeRel

namespace Formalism.L2.SG.LsDatumA

open Formalism.MainNotions.S.Loc

section RG8

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]

theorem rgHyp_of (M : Model F E) (hM : M.OK) {r n : ℕ} {V : Type} [AddCommGroup V] [Module E V] (H : HermSp M V)
    (hn : Module.finrank E V = n) (t₁ : Term V M r) (f₂ f₂' : Fin (r + 1) → V)
    (φ : H.Wb t₁.f ≃ₗ[E] H.Wb f₂) (φ' : H.Wb t₁.f' ≃ₗ[E] H.Wb f₂') (hyp : LocalCountHypotheses H t₁ f₂ f₂' φ φ')
    (Λ₂ : Submodule M.L.O V) (hg : H.IsGeneric ⟨Λ₂, f₂, f₂', t₁.T, t₁.T'⟩)
    (hth : ThCond H t₁ ⟨⊥, f₂, f₂', t₁.T, t₁.T'⟩ Λ₂ φ φ')
    (θ : DDt H t₁ ≃ₗ[M.L.O] DDt H ⟨⊥, f₂, f₂', t₁.T, t₁.T'⟩)
    (hθ : ∀ m₁ m₂, θ (ddMk H t₁ m₁) = ddMk H _ m₂ ↔ GlueRel H t₁ ⟨⊥, f₂, f₂', t₁.T, t₁.T'⟩ Λ₂ φ φ' m₁ m₂) :
    ∃ ψ, RGHyp H t₁ ⟨⊥, f₂, f₂', t₁.T, t₁.T'⟩ Λ₂ ψ θ φ φ' := by
  have hT₁ := hyp.1.1
  have hT₂ := hg.1
  have hF₁ : Formalism.MainNotions.ThinScalesBound.FrameK H t₁.f t₁.T := ⟨hT₁.2.1.2.1, hT₁.2.1.2.2.1⟩
  have hF₁' : Formalism.MainNotions.ThinScalesBound.FrameK H t₁.f' t₁.T' := ⟨hT₁.2.2.1.2.1, hT₁.2.2.1.2.2.1⟩
  have hD₂ : IsUnit (H.Dl f₂ f₂' (r + 1)) := hT₂.2.2.2.1
  have hD₁ : IsUnit (H.Dl t₁.f t₁.f' (r + 1)) := hT₁.2.2.2.1
  obtain ⟨ψ, -, hψc⟩ := corrIso_holds M r n V H hn t₁ f₂ f₂' φ φ' hyp hD₂
  have hU₁ : IsCompl (Submodule.span E (Set.range (Sum.elim t₁.f t₁.f'))) (H.W0 t₁.f t₁.f') :=
    isCompl_span_frames_W0 H t₁.f t₁.f' t₁.T t₁.T' hF₁ hF₁' hD₁ (isUnit_Gdet H _ _ _ _ hT₁.2.2.2.2.1)
  have hU₂ : IsCompl (Submodule.span E (Set.range (Sum.elim f₂ f₂'))) (H.W0 f₂ f₂') :=
    isCompl_span_frames_W0 H f₂ f₂' t₁.T t₁.T' hyp.2.1 hyp.2.2.1 hD₂ (isUnit_Gdet H _ _ _ _ hT₂.2.2.2.2.1)
  have hZ₁ : IsUnit (H.Zhat t₁.f t₁.f').det := by rw [← Dl_succ]; exact hD₁
  have hZ₁' : IsUnit (H.Zhat t₁.f' t₁.f).det := det_Zhat_swap_unit H _ _ hZ₁
  have hzφ : φ (H.mkW t₁.f ⟨t₁.f (Fin.last r), z_mem_perpX H hF₁⟩) =
      H.mkW f₂ ⟨f₂ (Fin.last r), z_mem_perpX H hyp.2.1⟩ := by
    have e := hyp.2.2.2.2.1 ⟨_, z_mem_perpX H hF₁⟩ ⟨_, z_mem_perpX H hyp.2.1⟩ rfl rfl
    simpa using e
  have hzφ' : φ' (H.mkW t₁.f' ⟨t₁.f' (Fin.last r), z_mem_perpX H hF₁'⟩) =
      H.mkW f₂' ⟨f₂' (Fin.last r), z_mem_perpX H hyp.2.2.1⟩ := by
    have e := hyp.2.2.2.2.2 ⟨_, z_mem_perpX H hF₁'⟩ ⟨_, z_mem_perpX H hyp.2.2.1⟩ rfl rfl
    simpa using e
  obtain ⟨u, hu⟩ := hD₂
  have hoφ : φ (H.mkW t₁.f ⟨H.om' t₁.f t₁.f', om'_mem_perpX H _ _⟩) =
      ((↑u⁻¹ : E) * H.Dl t₁.f t₁.f' (r + 1)) • H.mkW f₂ ⟨H.om' f₂ f₂', om'_mem_perpX H _ _⟩ := by
    have e : H.Dl f₂ f₂' (r + 1) • φ (H.mkW t₁.f ⟨H.om' t₁.f t₁.f', om'_mem_perpX H _ _⟩) =
        H.Dl t₁.f t₁.f' (r + 1) • H.mkW f₂ ⟨H.om' f₂ f₂', om'_mem_perpX H _ _⟩ :=
      hyp.2.2.2.1.2.2.2.1 _ _ rfl rfl
    rw [← hu] at e
    calc φ (H.mkW t₁.f ⟨H.om' t₁.f t₁.f', om'_mem_perpX H _ _⟩)
        = (↑u⁻¹ : E) • ((u : E) • φ (H.mkW t₁.f ⟨H.om' t₁.f t₁.f', om'_mem_perpX H _ _⟩)) := by
          rw [smul_smul, Units.inv_mul, one_smul]
      _ = _ := by rw [e, smul_smul]
  obtain ⟨u', hu'⟩ : IsUnit (M.L.cj (H.Dl f₂ f₂' (r + 1))) := by rw [← hu]; exact (Units.isUnit u).map _
  have hoφ' : φ' (H.mkW t₁.f' ⟨H.om' t₁.f' t₁.f, om'_mem_perpX H _ _⟩) =
      ((↑u'⁻¹ : E) * M.L.cj (H.Dl t₁.f t₁.f' (r + 1))) • H.mkW f₂' ⟨H.om' f₂' f₂, om'_mem_perpX H _ _⟩ := by
    have e : M.L.cj (H.Dl f₂ f₂' (r + 1)) • φ' (H.mkW t₁.f' ⟨H.om' t₁.f' t₁.f, om'_mem_perpX H _ _⟩) =
        M.L.cj (H.Dl t₁.f t₁.f' (r + 1)) • H.mkW f₂' ⟨H.om' f₂' f₂, om'_mem_perpX H _ _⟩ :=
      hyp.2.2.2.1.2.2.2.2.1 _ _ (om'_swap H _ _) (om'_swap H _ _)
    rw [← hu'] at e
    calc φ' (H.mkW t₁.f' ⟨H.om' t₁.f' t₁.f, om'_mem_perpX H _ _⟩)
        = (↑u'⁻¹ : E) • ((u' : E) • φ' (H.mkW t₁.f' ⟨H.om' t₁.f' t₁.f, om'_mem_perpX H _ _⟩)) := by
          rw [smul_smul, Units.inv_mul, one_smul]
      _ = _ := by rw [e, smul_smul]
  have hC2'' := cond_second_of_iso H t₁.f' t₁.f f₂' f₂ t₁.T' t₁.T' hF₁' hyp.2.2.1 hZ₁' φ' _ hzφ' hoφ'
  refine ⟨ψ, {
    hU₂ := hU₂
    hU₁ := hU₁
    hsd₁ := hT₁.1
    hsd₂ := hT₂.1
    hMM₁ := Submodule.span_le.2 (by rintro _ ⟨i, rfl⟩; exact hyp.1.2.1 i)
    hMM₂ := Submodule.span_le.2 (by rintro _ ⟨i, rfl⟩; exact hg.2.1 i)
    hth := fun w => hth w (ψ w) ((hψc _ _).2 ⟨w.2, rfl⟩)
    hθ := ?_
    hsurj₁ := surj_MMsharp M hM H t₁ hyp.1 hU₁
    hC1 := fun w => by
      obtain ⟨_, _, c₁, _⟩ := (hψc w (ψ w)).2 ⟨w.2, rfl⟩
      exact c₁
    hC1' := fun w => by
      obtain ⟨_, _, _, c₂⟩ := (hψc w (ψ w)).2 ⟨w.2, rfl⟩
      exact c₂
    hC2 := cond_second_of_iso H t₁.f t₁.f' f₂ f₂' t₁.T t₁.T hF₁ hyp.2.1 hZ₁ φ _ hzφ hoφ
    hC2' := fun v hv hvp => by
      rw [← U_swap] at hv
      obtain ⟨v', hv', hv'p, e⟩ := hC2'' v hv hvp
      rw [U_swap] at hv'
      exact ⟨v', hv', hv'p, e⟩ }⟩
  intro m₁ m₂
  rw [hθ m₁ m₂]
  constructor
  · rintro ⟨n₁, n₂, hc, h1, h2⟩
    obtain ⟨hn₁, hψn⟩ := (hψc _ _).1 hc
    exact ⟨⟨n₁, hn₁⟩, h1, by rw [hψn]; exact h2⟩
  · rintro ⟨w, h1, h2⟩
    exact ⟨w, ψ w, (hψc _ _).2 ⟨w.2, rfl⟩, h1, h2⟩

theorem claimRG_at (M : Model F E) (r n : ℕ) (hM : M.OK) : ClaimRG M r n := by
  intro hsome V _ _ H hn t₁ f₂ f₂' φ φ' hyp Λ₂ hg hth θ hθ
  obtain ⟨g, hs⟩ := Option.isSome_iff_exists.1 hsome
  obtain ⟨ψ, D⟩ := rgHyp_of M hM H hn t₁ f₂ f₂' φ φ' hyp Λ₂ hg hth θ hθ
  have core1 := fun hI => Set.Subset.antisymm (rg_fwd_sub H g D hI) (rg_fwd_sup H g D hI)
  have core2 := fun hG => Set.Subset.antisymm (rg_bwd_sub H g D hG) (rg_bwd_sup H g D hG)
  have hL1 := Lset_eq_snd H hM g hs t₁ hyp.1 D.hU₁
  have hL1' := Lset_eq_fst H hM g hs t₁ hyp.1 D.hU₁
  have hL2 := Lset_eq_snd H hM g hs (⟨Λ₂, f₂, f₂', t₁.T, t₁.T'⟩ : Term V M r) hg D.hU₂
  have hL2' := Lset_eq_fst H hM g hs (⟨Λ₂, f₂, f₂', t₁.T, t₁.T'⟩ : Term V M r) hg D.hU₂
  constructor
  · intro hR
    refine ⟨fun h => absurd (hs.symm.trans h) (by simp), fun g' hg' => ?_⟩
    rw [Option.some.inj (hg'.symm.trans hs)]
    exact core1 (hR.2.2.2.2 g hs)
  · rintro ⟨-, hGR⟩
    have hI := core2 (hGR g hs)
    have e : φ '' (Prod.snd '' H.iotaGraph g t₁) = Prod.snd '' (Prod.map φ' φ '' H.iotaGraph g t₁) := by
      rw [Set.image_image, Set.image_image]
      rfl
    have e' : φ' '' (Prod.fst '' H.iotaGraph g t₁) = Prod.fst '' (Prod.map φ' φ '' H.iotaGraph g t₁) := by
      rw [Set.image_image, Set.image_image]
      rfl
    refine ⟨(congrArg (φ '' ·) hL1).trans (e.trans ((congrArg (Prod.snd '' ·) hI).trans hL2.symm)),
      hyp.2.2.2.2.1,
      (congrArg (φ' '' ·) hL1').trans (e'.trans ((congrArg (Prod.fst '' ·) hI).trans hL2'.symm)),
      hyp.2.2.2.2.2, fun g' hg' => ?_⟩
    rw [Option.some.inj (hg'.symm.trans hs)]
    exact hI

theorem claimR_at (M : Model F E) (r n : ℕ) (hM : M.OK) : ClaimR M r n :=
  claimR_of_modes M r n (claimRL_at M r n hM) (claimRG_at M r n hM)

theorem localCount_of_module (M : Model F E) (r n : ℕ) (hM : M.OK) (h0 : ModSide0 M r n M.split.isSome)
    (hU : ModSideU M r n M.split.isSome) : Formalism.MainNotions.ThinScalesBound.FamilyLocalModel M r n :=
  localCount_of_glue M r n hM (PI.LocCntLat.GE.glueEta_holds M r) (PI.LocCntLat.GC.glueConv_holds M r)
    (genOfPrim_holds M r n) (claimR_at M r n hM) h0 hU

theorem globalCount_of_module (D : Formalism.BasicNotions.D7)
    (h0 : Formalism.MainNotions.ThinScalesBound.AllLoc (fun M => ModSide0 M D.R.rS D.R.r M.split.isSome))
    (hU : Formalism.MainNotions.ThinScalesBound.AllLoc (fun M => ModSideU M D.R.rS D.R.r M.split.isSome)) : Formalism.MainNotions.ThinScalesBound.T2 D := by
  intro F _ _ _ E _ _ _ _ M hM
  exact localCount_of_module M D.R.rS D.R.r hM (h0 F E M hM) (hU F E M hM)

end RG8

end Formalism.L2.SG.LsDatumA
