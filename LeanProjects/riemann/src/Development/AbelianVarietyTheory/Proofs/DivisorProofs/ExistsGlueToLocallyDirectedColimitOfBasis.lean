import Mathlib
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsSchemeOfThickenings
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PreimageUpOpen

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

noncomputable section
namespace GlobalTheory.ColimitGlue

set_option backward.isDefEq.respectTransparency false in

theorem exists_glue {B₀ : Scheme.{0}} (𝒰 : Set B₀.Opens) (F : 𝒰 ⥤ Scheme.{0})
    [∀ {U V : 𝒰} (f : U ⟶ V), IsOpenImmersion (F.map f)] [(F ⋙ Scheme.forget).IsLocallyDirected]
    (X : Scheme.{0}) (G : B₀.Opens → X.Opens) (hG : Monotone G)
    (hbas : ∀ U ∈ 𝒰, ∀ V ∈ 𝒰, ∀ x : X, x ∈ G U → x ∈ G V → ∃ W ∈ 𝒰, x ∈ G W ∧ W ≤ U ∧ W ≤ V)
    (hc : ∀ x : X, ∃ U ∈ 𝒰, x ∈ G U)
    (e : ∀ U : 𝒰, (G U.1).toScheme ⟶ F.obj U)
    (hnat : ∀ {U V : 𝒰} (h : U.1 ≤ V.1),
      X.homOfLE (hG h) ≫ e V = e U ≫ F.map (homOfLE (show U ≤ V from h))) :
    ∃ j : X ⟶ colimit F, ∀ U : 𝒰, (G U.1).ι ≫ j = e U ≫ colimit.ι F U := by
  have hcov : TopologicalSpace.IsOpenCover (fun U : 𝒰 ↦ G U.1) :=
    eq_top_iff.2 fun x _ =>
      TopologicalSpace.Opens.mem_iSup.2 (by obtain ⟨U, hU, hx⟩ := hc x; exact ⟨⟨U, hU⟩, hx⟩)
  let 𝒱 : X.OpenCover := X.openCoverOfIsOpenCover (fun U : 𝒰 ↦ G U.1) hcov
  let j : X ⟶ colimit F := 𝒱.glueMorphisms (fun U ↦ e U ≫ colimit.ι F U) (by
    intro U V
    apply Scheme.hom_ext_of_forall
    intro x
    have hx : (pullback.fst (𝒱.f U) (𝒱.f V) x).1 = (pullback.snd (𝒱.f U) (𝒱.f V) x).1 :=
      congr($(pullback.condition (f := 𝒱.f U) (g := 𝒱.f V)) x)
    obtain ⟨W, hW, hxW, h1, h2⟩ := hbas U.1 U.2 V.1 V.2 _ (pullback.fst (𝒱.f U) (𝒱.f V) x).2
      (hx ▸ (pullback.snd (𝒱.f U) (𝒱.f V) x).2)
    let α : (G W).toScheme ⟶ pullback (𝒱.f U) (𝒱.f V) :=
      pullback.lift (X.homOfLE (hG h1)) (X.homOfLE (hG h2))
        ((X.homOfLE_ι (hG h1)).trans (X.homOfLE_ι (hG h2)).symm)
    have hα1 : α ≫ pullback.fst _ _ = X.homOfLE (hG h1) := pullback.lift_fst _ _ _
    have hα2 : α ≫ pullback.snd _ _ = X.homOfLE (hG h2) := pullback.lift_snd _ _ _
    have : IsOpenImmersion (α ≫ pullback.fst _ _) := by rw [hα1]; infer_instance
    have : IsOpenImmersion α := .of_comp _ (pullback.fst _ _)
    refine ⟨α.opensRange, ⟨⟨_, hxW⟩, ?_⟩, ?_⟩
    · apply (pullback.fst (𝒱.f U) (𝒱.f V)).isOpenEmbedding.injective
      rw [← Scheme.Hom.comp_apply, hα1]
      exact Subtype.ext (Scheme.homOfLE_apply _ _)
    · rw [← cancel_epi α.isoOpensRange.hom]
      simp only [Scheme.Hom.isoOpensRange_hom_ι_assoc]
      rw [reassoc_of% hα1, reassoc_of% hα2, reassoc_of% (hnat (U := ⟨W, hW⟩) (V := U) h1),
        reassoc_of% (hnat (U := ⟨W, hW⟩) (V := V) h2), colimit.w, colimit.w])
  exact ⟨j, fun U ↦ 𝒱.ι_glueMorphisms _ _ U⟩

end GlobalTheory.ColimitGlue
