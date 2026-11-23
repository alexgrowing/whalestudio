import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.LsDatumACorr

noncomputable section

open ValuativeRel Matrix

namespace Formalism.L2.SG.LsDatumA

open Formalism.MainNotions.S.Loc

section CorrProof

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]

theorem Dl_succ {M : Model F E} {V : Type} [AddCommGroup V] [Module E V] (H : HermSp M V) {r : ℕ}
    (f f' : Fin (r + 1) → V) : H.Dl f f' (r + 1) = (H.Zhat f f').det := by
  unfold HermSp.Dl
  rw [dif_pos le_rfl]
  congr 1

theorem mkW_eq_of_sub_mem {M : Model F E} {V : Type} [AddCommGroup V] [Module E V] (H : HermSp M V) {r : ℕ}
    {f : Fin (r + 1) → V} {x y : ↥(H.perp (H.X f))} (h : (x : V) - y ∈ H.X f) : H.mkW f x = H.mkW f y := by
  unfold HermSp.mkW
  rw [Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq]
  simpa using h

theorem corrIso_holds (M : Model F E) (r n : ℕ) : CorrIso M r n := by
  intro V _ _ H hn t₁ f₂ f₂' φ φ' hyp hD₂
  obtain ⟨hg₁, hF₂, hF₂', hI, hz, hz'⟩ := hyp
  have hT1 := hg₁.1
  have hF₁ : Formalism.MainNotions.ThinScalesBound.FrameK H t₁.f t₁.T := ⟨hT1.2.1.2.1, hT1.2.1.2.2.1⟩
  have hF₁' : Formalism.MainNotions.ThinScalesBound.FrameK H t₁.f' t₁.T' := ⟨hT1.2.2.1.2.1, hT1.2.2.1.2.2.1⟩
  have hD₁ : IsUnit (H.Dl t₁.f t₁.f' (r + 1)) := hT1.2.2.2.1
  have hG₁ : IsUnit (H.Gdet t₁.f t₁.f' t₁.T t₁.T') := isUnit_Gdet H _ _ _ _ hT1.2.2.2.2.1
  obtain ⟨hIs, -, hW0c, hom', -, hκ⟩ := hI
  have hG₂ : IsUnit (H.Gdet f₂ f₂' t₁.T t₁.T') := by
    have e := Gdet_rel H t₁.f t₁.f' f₂ f₂' t₁.T t₁.T' hκ
    have hN₁ : IsUnit (H.normE (H.Dl t₁.f t₁.f' (r + 1))) := hD₁.mul (hD₁.map M.L.cj)
    have hN₂ : IsUnit (H.normE (H.Dl f₂ f₂' (r + 1))) := hD₂.mul (hD₂.map M.L.cj)
    have h3 : IsUnit (H.Gdet f₂ f₂' t₁.T t₁.T' * H.normE (H.Dl t₁.f t₁.f' (r + 1))) := by
      rw [e]
      exact hN₂.mul hG₁
    exact isUnit_of_mul_isUnit_left h3
  have hU₁ := isCompl_span_frames_W0 H t₁.f t₁.f' t₁.T t₁.T' hF₁ hF₁' hD₁ hG₁
  have hU₂ := isCompl_span_frames_W0 H f₂ f₂' t₁.T t₁.T' hF₂ hF₂' hD₂ hG₂
  have hXU : ∀ g g' : Fin (r + 1) → V, H.X g ≤ Submodule.span E (Set.range (Sum.elim g g')) :=
    fun g g' => Submodule.span_mono (by rintro _ ⟨j, rfl⟩; exact ⟨Sum.inl j.castSucc, rfl⟩)
  have huniq : ∀ (a b : V) (ha : a ∈ H.W0 f₂ f₂') (hb : b ∈ H.W0 f₂ f₂'),
      H.mkW f₂ ⟨a, mem_perp_isotropicSpan_of_mem_framePerp H ha⟩ = H.mkW f₂ ⟨b, mem_perp_isotropicSpan_of_mem_framePerp H hb⟩ → a = b := by
    intro a b ha hb hab
    have h1 := sub_mem_X_of_mkW_eq H hab
    exact sub_eq_zero.1 ((Submodule.disjoint_def.1 hU₂.disjoint) _ (hXU f₂ f₂' h1) (Submodule.sub_mem _ ha hb))
  have hex : ∀ w : ↥(H.W0 t₁.f t₁.f'), ∃ w₂ : ↥(H.W0 f₂ f₂'),
      φ (H.mkW t₁.f ⟨w, mem_perp_isotropicSpan_of_mem_framePerp H w.2⟩) = H.mkW f₂ ⟨w₂, mem_perp_isotropicSpan_of_mem_framePerp H w₂.2⟩ ∧
      φ' (H.mkW t₁.f' ⟨w, mem_perp_isotropicSpan_of_mem_framePerp' H w.2⟩) = H.mkW f₂' ⟨w₂, mem_perp_isotropicSpan_of_mem_framePerp' H w₂.2⟩ := by
    intro w
    obtain ⟨w₂, hw₂, s1, s2⟩ := hW0c w w.2
    refine ⟨⟨w₂, hw₂⟩, ?_, ?_⟩
    · have := s1 ⟨w, mem_perp_isotropicSpan_of_mem_framePerp H w.2⟩ ⟨w₂, mem_perp_isotropicSpan_of_mem_framePerp H hw₂⟩ rfl rfl
      simpa using this
    · have := s2 ⟨w, mem_perp_isotropicSpan_of_mem_framePerp' H w.2⟩ ⟨w₂, mem_perp_isotropicSpan_of_mem_framePerp' H hw₂⟩ rfl rfl
      simpa using this
  choose ψf hψf using hex
  have hψadd : ∀ a b, ψf (a + b) = ψf a + ψf b := by
    intro a b
    apply Subtype.ext
    apply huniq _ _ (ψf (a + b)).2 (ψf a + ψf b).2
    rw [← (hψf (a + b)).1]
    have e : (⟨((a + b : ↥(H.W0 t₁.f t₁.f')) : V), mem_perp_isotropicSpan_of_mem_framePerp H (a + b).2⟩ : ↥(H.perp (H.X t₁.f))) =
        ⟨a, mem_perp_isotropicSpan_of_mem_framePerp H a.2⟩ + ⟨b, mem_perp_isotropicSpan_of_mem_framePerp H b.2⟩ := Subtype.ext rfl
    have e2 : (⟨((ψf a + ψf b : ↥(H.W0 f₂ f₂')) : V), mem_perp_isotropicSpan_of_mem_framePerp H (ψf a + ψf b).2⟩ : ↥(H.perp (H.X f₂))) =
        ⟨ψf a, mem_perp_isotropicSpan_of_mem_framePerp H (ψf a).2⟩ + ⟨ψf b, mem_perp_isotropicSpan_of_mem_framePerp H (ψf b).2⟩ := Subtype.ext rfl
    rw [e, e2, map_add, map_add, map_add, (hψf a).1, (hψf b).1]
  have hψsmul : ∀ (c : E) a, ψf (c • a) = c • ψf a := by
    intro c a
    apply Subtype.ext
    apply huniq _ _ (ψf (c • a)).2 (c • ψf a).2
    rw [← (hψf (c • a)).1]
    have e : (⟨((c • a : ↥(H.W0 t₁.f t₁.f')) : V), mem_perp_isotropicSpan_of_mem_framePerp H (c • a).2⟩ : ↥(H.perp (H.X t₁.f))) =
        c • ⟨a, mem_perp_isotropicSpan_of_mem_framePerp H a.2⟩ := Subtype.ext rfl
    have e2 : (⟨((c • ψf a : ↥(H.W0 f₂ f₂')) : V), mem_perp_isotropicSpan_of_mem_framePerp H (c • ψf a).2⟩ : ↥(H.perp (H.X f₂))) =
        c • ⟨ψf a, mem_perp_isotropicSpan_of_mem_framePerp H (ψf a).2⟩ := Subtype.ext rfl
    rw [e, e2, map_smul, map_smul, map_smul, (hψf a).1]
  let ψL : ↥(H.W0 t₁.f t₁.f') →ₗ[E] ↥(H.W0 f₂ f₂') :=
    { toFun := ψf, map_add' := hψadd, map_smul' := hψsmul }
  have hinj : Function.Injective ψL := by
    intro a b hab
    have hab' : ψf a = ψf b := hab
    have e : H.mkW t₁.f ⟨a, mem_perp_isotropicSpan_of_mem_framePerp H a.2⟩ = H.mkW t₁.f ⟨b, mem_perp_isotropicSpan_of_mem_framePerp H b.2⟩ :=
      φ.injective (by rw [(hψf a).1, (hψf b).1, hab'])
    have h1 := sub_mem_X_of_mkW_eq H e
    exact Subtype.ext (sub_eq_zero.1 ((Submodule.disjoint_def.1 hU₁.disjoint) _ (hXU t₁.f t₁.f' h1)
      (Submodule.sub_mem _ a.2 b.2)))
  have hsurj : Function.Surjective ψL := by
    intro w₂
    obtain ⟨y, hy⟩ := Submodule.Quotient.mk_surjective _ (φ.symm (H.mkW f₂ ⟨w₂, mem_perp_isotropicSpan_of_mem_framePerp H w₂.2⟩))
    have hy' : φ (H.mkW t₁.f y) = H.mkW f₂ ⟨w₂, mem_perp_isotropicSpan_of_mem_framePerp H w₂.2⟩ := by
      have : H.mkW t₁.f y = φ.symm (H.mkW f₂ ⟨w₂, mem_perp_isotropicSpan_of_mem_framePerp H w₂.2⟩) := hy
      rw [this, LinearEquiv.apply_symm_apply]
    have hyU : (y : V) ∈ Submodule.span E (Set.range (Sum.elim t₁.f t₁.f')) ⊔ H.W0 t₁.f t₁.f' := by
      rw [hU₁.sup_eq_top]
      exact Submodule.mem_top
    obtain ⟨u, hu, w, hw, huw⟩ := Submodule.mem_sup.1 hyU
    have hup : u ∈ H.perp (H.X t₁.f) := by
      have : u = (y : V) - w := by rw [← huw]; abel
      rw [this]
      exact Submodule.sub_mem _ y.2 (mem_perp_isotropicSpan_of_mem_framePerp H hw)
    have hZ₁ : IsUnit (H.Zhat t₁.f t₁.f').det := by rw [← Dl_succ]; exact hD₁
    obtain ⟨x, hx, β, γ, hxe⟩ := decomp_U_perpX H hF₁ hZ₁ hu hup
    refine ⟨⟨w, hw⟩, ?_⟩
    set D₂ := H.Dl f₂ f₂' (r + 1)
    set D₁ := H.Dl t₁.f t₁.f' (r + 1)
    let zP₁ : ↥(H.perp (H.X t₁.f)) := ⟨t₁.f (Fin.last r), z_mem_perpX H hF₁⟩
    let oP₁ : ↥(H.perp (H.X t₁.f)) := ⟨H.om' t₁.f t₁.f', om'_mem_perpX H _ _⟩
    let zP₂ : ↥(H.perp (H.X f₂)) := ⟨f₂ (Fin.last r), z_mem_perpX H hF₂⟩
    let oP₂ : ↥(H.perp (H.X f₂)) := ⟨H.om' f₂ f₂', om'_mem_perpX H _ _⟩
    let wP : ↥(H.perp (H.X t₁.f)) := ⟨w, mem_perp_isotropicSpan_of_mem_framePerp H hw⟩
    let vP : ↥(H.perp (H.X f₂)) := ⟨ψf ⟨w, hw⟩, mem_perp_isotropicSpan_of_mem_framePerp H (ψf ⟨w, hw⟩).2⟩
    have hq₁ : H.mkW t₁.f y = H.mkW t₁.f (β • zP₁ + γ • oP₁ + wP) := by
      apply mkW_eq_of_sub_mem
      show (y : V) - (β • t₁.f (Fin.last r) + γ • H.om' t₁.f t₁.f' + w) ∈ H.X t₁.f
      rw [← huw, hxe]
      convert hx using 1
      abel
    have hz1 : φ (H.mkW t₁.f zP₁) = H.mkW f₂ zP₂ := by
      have := hz zP₁ zP₂ rfl rfl
      simpa using this
    have ho0 : D₂ • φ (H.mkW t₁.f oP₁) = D₁ • H.mkW f₂ oP₂ := by
      have := hom' oP₁ oP₂ rfl rfl
      simpa using this
    have ho1 : φ (H.mkW t₁.f oP₁) = (Ring.inverse D₂ * D₁) • H.mkW f₂ oP₂ := by
      rw [mul_smul, ← ho0, smul_smul, Ring.inverse_mul_cancel _ hD₂, one_smul]
    have hw1 : φ (H.mkW t₁.f wP) = H.mkW f₂ vP := (hψf ⟨w, hw⟩).1
    have hq₂ : H.mkW f₂ ⟨w₂, mem_perp_isotropicSpan_of_mem_framePerp H w₂.2⟩ =
        H.mkW f₂ (β • zP₂ + (γ * (Ring.inverse D₂ * D₁)) • oP₂ + vP) := by
      rw [← hy', hq₁]
      simp only [map_add, map_smul, hz1, ho1, hw1, smul_smul]
    have hd := sub_mem_X_of_mkW_eq H hq₂
    have hU2mem : (w₂ : V) - (ψf ⟨w, hw⟩ : V) ∈ Submodule.span E (Set.range (Sum.elim f₂ f₂')) := by
      have e : (w₂ : V) - (ψf ⟨w, hw⟩ : V) =
          ((w₂ : V) - ((β • zP₂ + (γ * (Ring.inverse D₂ * D₁)) • oP₂ + vP : ↥(H.perp (H.X f₂))) : V)) +
            (β • f₂ (Fin.last r) + (γ * (Ring.inverse D₂ * D₁)) • H.om' f₂ f₂') := by
        simp only [Submodule.coe_add, Submodule.coe_smul, zP₂, oP₂, vP]
        abel
      rw [e]
      exact Submodule.add_mem _ (hXU f₂ f₂' hd) (Submodule.add_mem _
        (Submodule.smul_mem _ _ (Submodule.subset_span ⟨Sum.inl (Fin.last r), rfl⟩))
        (Submodule.smul_mem _ _ (om'_mem_U H f₂ f₂')))
    have h0 := (Submodule.disjoint_def.1 hU₂.disjoint) _ hU2mem (Submodule.sub_mem _ w₂.2 (ψf ⟨w, hw⟩).2)
    exact Subtype.ext (sub_eq_zero.1 h0).symm
  refine ⟨LinearEquiv.ofBijective ψL ⟨hinj, hsurj⟩, fun a b => ?_, fun n₁ n₂ => ?_⟩
  · show H.h ((ψf a : ↥(H.W0 f₂ f₂')) : V) ((ψf b : ↥(H.W0 f₂ f₂')) : V) = H.h a b
    exact hIs ⟨a, mem_perp_isotropicSpan_of_mem_framePerp H a.2⟩ ⟨b, mem_perp_isotropicSpan_of_mem_framePerp H b.2⟩ ⟨ψf a, mem_perp_isotropicSpan_of_mem_framePerp H (ψf a).2⟩
      ⟨ψf b, mem_perp_isotropicSpan_of_mem_framePerp H (ψf b).2⟩ (hψf a).1 (hψf b).1
  · constructor
    · rintro ⟨h₁, h₂, c1, -⟩
      refine ⟨h₁, ?_⟩
      show ((ψf ⟨n₁, h₁⟩ : ↥(H.W0 f₂ f₂')) : V) = n₂
      exact huniq _ _ (ψf ⟨n₁, h₁⟩).2 h₂ ((hψf ⟨n₁, h₁⟩).1.symm.trans c1)
    · rintro ⟨h₁, rfl⟩
      exact ⟨h₁, (ψf ⟨n₁, h₁⟩).2, (hψf ⟨n₁, h₁⟩).1, (hψf ⟨n₁, h₁⟩).2⟩

end CorrProof

end Formalism.L2.SG.LsDatumA
