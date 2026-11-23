import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DetZhatSwapUnit
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.LsDatumAInj
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.LsDatumAGlue

noncomputable section

open ValuativeRel

namespace Formalism.L2.SG.LsDatumA

open Formalism.MainNotions.S.Loc

section T2CR

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]

def ClaimRL (M : Model F E) (r n : ℕ) : Prop := M.split = none → ClaimR M r n

def ClaimRG (M : Model F E) (r n : ℕ) : Prop := M.split.isSome = true → ClaimR M r n

theorem claimR_of_modes (M : Model F E) (r n : ℕ) (hL : ClaimRL M r n) (hG : ClaimRG M r n) :
    ClaimR M r n := by
  rcases hs : M.split with _ | g
  · exact hL hs
  · exact hG (by rw [hs]; rfl)

theorem X_le_span_left {M : Model F E} {V : Type} [AddCommGroup V] [Module E V] (H : HermSp M V) {r : ℕ}
    (f f' : Fin (r + 1) → V) : H.X f ≤ Submodule.span E (Set.range (Sum.elim f f')) :=
  Submodule.span_le.2 (by rintro _ ⟨j, rfl⟩; exact Submodule.subset_span ⟨Sum.inl j.castSucc, rfl⟩)

theorem X_le_span_right {M : Model F E} {V : Type} [AddCommGroup V] [Module E V] (H : HermSp M V) {r : ℕ}
    (f f' : Fin (r + 1) → V) : H.X f' ≤ Submodule.span E (Set.range (Sum.elim f f')) :=
  Submodule.span_le.2 (by rintro _ ⟨j, rfl⟩; exact Submodule.subset_span ⟨Sum.inr j.castSucc, rfl⟩)

theorem surj_MMsharp (M : Model F E) (hM : M.OK) {V : Type} [AddCommGroup V] [Module E V] (H : HermSp M V)
    {r : ℕ} (t : Term V M r) (hgen : H.IsGeneric t)
    (hU : IsCompl (Submodule.span E (Set.range (Sum.elim t.f t.f'))) (H.W0 t.f t.f')) :
    ∀ m : ↥(MMsharp H t), ∃ w : ↥(H.W0 t.f t.f'), (m : V) + w ∈ t.abelian₂ := by
  intro m
  have hU' : IsCompl (Submodule.span E (Set.range (Sum.elim t.f t.f')))
      (H.perp (Submodule.span E (Set.range (Sum.elim t.f t.f')))) := by
    rw [← hermSp_W0_eq_perp_span_range_MMfam]
    exact hU
  have hmU : (m : V) ∈ Submodule.span E (Set.range (Sum.elim t.f t.f')) := spanMM_le_U H t m.2.1
  obtain ⟨x, hx, hpx⟩ := ((local_hermitian_glue F E M hM V H t.abelian₂ hgen.1.1 _ hU').1 (m : V) hmU).2
    (fun y hy hyU => m.2.2 y (hgen.2.2.2 y hy (span_frames_le_MM H t hyU)))
  have hx' : x ∈ Submodule.span E (Set.range (Sum.elim t.f t.f')) ⊔
      H.perp (Submodule.span E (Set.range (Sum.elim t.f t.f'))) := by
    rw [hU'.sup_eq_top]
    exact Submodule.mem_top
  obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.1 hx'
  have hpa : ((Submodule.linearProjOfIsCompl _ _ hU' x :
      ↥(Submodule.span E (Set.range (Sum.elim t.f t.f')))) : V) = a := by
    rw [← hab, map_add]
    have e1 := Submodule.projectionOnto_apply_left hU' ⟨a, ha⟩
    have e2 := Submodule.projectionOnto_apply_right hU' ⟨b, hb⟩
    simp only [Submodule.linearProjOfIsCompl] at *
    rw [e1, e2, add_zero]
  have hma : (m : V) = a := by rw [← hpx, hpa]
  have hbW : b ∈ H.W0 t.f t.f' := by rw [hermSp_W0_eq_perp_span_range_MMfam]; exact hb
  refine ⟨⟨b, hbW⟩, ?_⟩
  show (m : V) + b ∈ t.abelian₂
  rw [hma, hab]
  exact hx

theorem claimRL_at (M : Model F E) (r n : ℕ) (hM : M.OK) : ClaimRL M r n := by
  intro hs V _ _ H hn t₁ f₂ f₂' φ φ' hyp Λ₂ hg hth θ hθ
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
  have hMM₁ : MMo H t₁ ≤ t₁.abelian₂ := Submodule.span_le.2 (by rintro _ ⟨i, rfl⟩; exact hyp.1.2.1 i)
  have hMM₂ : MMo H (⟨⊥, f₂, f₂', t₁.T, t₁.T'⟩ : Term V M r) ≤ Λ₂ :=
    Submodule.span_le.2 (by rintro _ ⟨i, rfl⟩; exact hg.2.1 i)
  have hth' : ∀ w : ↥(H.W0 t₁.f t₁.f'), (w : V) ∈ t₁.abelian₂ ↔ (ψ w : V) ∈ Λ₂ :=
    fun w => hth w (ψ w) ((hψc _ _).2 ⟨w.2, rfl⟩)
  have hθ' : ∀ m₁ m₂, θ (ddMk H t₁ m₁) = ddMk H (⟨⊥, f₂, f₂', t₁.T, t₁.T'⟩ : Term V M r) m₂ ↔
      ∃ w : ↥(H.W0 t₁.f t₁.f'), (m₁ : V) + w ∈ t₁.abelian₂ ∧ (m₂ : V) + ψ w ∈ Λ₂ := by
    intro m₁ m₂
    rw [hθ m₁ m₂]
    constructor
    · rintro ⟨n₁, n₂, hc, h1, h2⟩
      obtain ⟨hn₁, hψn⟩ := (hψc _ _).1 hc
      exact ⟨⟨n₁, hn₁⟩, h1, by rw [hψn]; exact h2⟩
    · rintro ⟨w, h1, h2⟩
      exact ⟨w, ψ w, (hψc _ _).2 ⟨w.2, rfl⟩, h1, h2⟩
  have hsurj₁ := surj_MMsharp M hM H t₁ hyp.1 hU₁

  have hC1 : ∀ w : ↥(H.W0 t₁.f t₁.f'),
      φ (H.mkW t₁.f ⟨w, mem_perp_isotropicSpan_of_mem_framePerp H w.2⟩) = H.mkW f₂ ⟨ψ w, mem_perp_isotropicSpan_of_mem_framePerp H (ψ w).2⟩ := by
    intro w
    obtain ⟨_, _, c₁, _⟩ := (hψc w (ψ w)).2 ⟨w.2, rfl⟩
    exact c₁
  have hC1' : ∀ w : ↥(H.W0 t₁.f t₁.f'),
      φ' (H.mkW t₁.f' ⟨w, mem_perp_isotropicSpan_of_mem_framePerp' H w.2⟩) = H.mkW f₂' ⟨ψ w, mem_perp_isotropicSpan_of_mem_framePerp' H (ψ w).2⟩ := by
    intro w
    obtain ⟨_, _, _, c₂⟩ := (hψc w (ψ w)).2 ⟨w.2, rfl⟩
    exact c₂
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
  have hC2 := cond_second_of_iso H t₁.f t₁.f' f₂ f₂' t₁.T t₁.T hF₁ hyp.2.1 hZ₁ φ _ hzφ hoφ
  have hC2'' := cond_second_of_iso H t₁.f' t₁.f f₂' f₂ t₁.T' t₁.T' hF₁' hyp.2.2.1 hZ₁' φ' _ hzφ' hoφ'
  have hC2' : ∀ u ∈ Submodule.span E (Set.range (Sum.elim t₁.f t₁.f')), ∀ hu : u ∈ H.perp (H.X t₁.f'),
      ∃ u' ∈ Submodule.span E (Set.range (Sum.elim f₂ f₂')), ∃ hu' : u' ∈ H.perp (H.X f₂'),
        φ' (H.mkW t₁.f' ⟨u, hu⟩) = H.mkW f₂' ⟨u', hu'⟩ := by
    intro v hv hvp
    rw [← U_swap] at hv
    obtain ⟨v', hv', hv'p, e⟩ := hC2'' v hv hvp
    rw [U_swap] at hv'
    exact ⟨v', hv', hv'p, e⟩
  have hL := claimR_side H t₁ ⟨⊥, f₂, f₂', t₁.T, t₁.T'⟩ Λ₂ ψ hU₂ hU₁ hT₁.1 hT₂.1 hMM₁ hMM₂ hth' θ hθ' hsurj₁
    t₁.f f₂ (X_le_span_left H f₂ f₂') (fun _ h => mem_perp_isotropicSpan_of_mem_framePerp H h) (fun _ h => mem_perp_isotropicSpan_of_mem_framePerp H h) φ hC1 hC2
  have hL' := claimR_side H t₁ ⟨⊥, f₂, f₂', t₁.T, t₁.T'⟩ Λ₂ ψ hU₂ hU₁ hT₁.1 hT₂.1 hMM₁ hMM₂ hth' θ hθ' hsurj₁
    t₁.f' f₂' (X_le_span_right H f₂ f₂') (fun _ h => mem_perp_isotropicSpan_of_mem_framePerp' H h) (fun _ h => mem_perp_isotropicSpan_of_mem_framePerp' H h) φ' hC1' hC2'
  constructor
  · intro hR
    refine ⟨fun _ => ⟨hL.1 hR.1, hL'.1 hR.2.2.1⟩, fun g hg => ?_⟩
    rw [hs] at hg
    exact absurd hg (by simp)
  · rintro ⟨h1, -⟩
    obtain ⟨a, b⟩ := h1 hs
    refine ⟨hL.2 a, hyp.2.2.2.2.1, hL'.2 b, hyp.2.2.2.2.2, fun g hg => ?_⟩
    rw [hs] at hg
    exact absurd hg (by simp)

end T2CR

end Formalism.L2.SG.LsDatumA
