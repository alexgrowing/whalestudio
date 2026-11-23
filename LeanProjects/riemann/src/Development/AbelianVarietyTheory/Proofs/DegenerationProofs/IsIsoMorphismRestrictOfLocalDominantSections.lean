import Mathlib
import Development.AbelianVarietyTheory.Definitions.Degenerations.InducedModelMorphismCompStructureMap
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsIntegrallyClosedStalkOfRingOn
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.HomExtOfIsOpenImmersion

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical

noncomputable section
namespace GlobalTheory.ZH

open GlobalTheory.Points

theorem isIso_pullback_snd_of_dominant_section {X Y V : Scheme.{0}} (f : X ⟶ Y) [IsSeparated f] [IsReduced X]
    (q : V ⟶ Y) [IsOpenImmersion q] (g : V ⟶ X) [IsDominant g] (h : g ≫ f = q) : IsIso (pullback.snd f q) := by
  let σ : V ⟶ pullback f q := pullback.lift g (𝟙 V) (by rw [h, Category.id_comp])
  have e1 : σ ≫ pullback.fst f q = g := pullback.lift_fst _ _ _
  have e2 : σ ≫ pullback.snd f q = 𝟙 V := pullback.lift_snd _ _ _
  have : IsReduced (pullback f q) := isReduced_of_isOpenImmersion (pullback.fst f q)
  have : IsDominant (σ ≫ pullback.fst f q) := e1 ▸ inferInstance
  have : IsDominant σ := IsDominant.of_comp_of_isOpenImmersion σ (pullback.fst f q)
  refine ⟨σ, ?_, e2⟩
  refine ext_of_isDominant_of_isSeparated (pullback.snd f q) ?_ σ ?_
  · rw [Category.assoc, e2, Category.comp_id, Category.id_comp]
  · rw [← Category.assoc, e2, Category.id_comp, Category.comp_id]

theorem isIso_of_local_dominant_sections {X Y : Scheme.{0}} (f : X ⟶ Y) [IsSeparated f] [IsReduced X]
    (h : ∀ y : Y, ∃ (V : Scheme.{0}) (q : V ⟶ Y) (_ : IsOpenImmersion q) (g : V ⟶ X),
      y ∈ Set.range q ∧ IsDominant g ∧ g ≫ f = q) : IsIso f := by
  choose V q hq g hy hg e using h
  let 𝒰 : Y.OpenCover := Scheme.Cover.mkOfCovers Y V q fun y => ⟨y, hy y⟩
  exact IsZariskiLocalAtTarget.of_openCover (P := MorphismProperty.isomorphisms _) 𝒰 fun y =>
    haveI := hq y
    haveI := hg y
    isIso_pullback_snd_of_dominant_section f (q y) (g y) (e y)

theorem isIso_morphismRestrict_of_local_dominant_sections {X Y : Scheme.{0}} (f : X ⟶ Y) [IsSeparated f] [IsReduced X]
    (W : Y.Opens) (h : ∀ y ∈ W, ∃ (V : Scheme.{0}) (q : V ⟶ Y) (_ : IsOpenImmersion q) (g : V ⟶ X),
      y ∈ Set.range q ∧ Set.range q ⊆ W ∧ IsDominant g ∧ g ≫ f = q) : IsIso (f ∣_ W) := by
  have : IsSeparated (f ∣_ W) := IsZariskiLocalAtTarget.restrict (P := @IsSeparated) ‹_› W
  refine isIso_of_local_dominant_sections _ fun y => ?_
  obtain ⟨V, q, hq, g, ⟨v, hv⟩, hW, hg, e⟩ := h y.1 y.2
  have h1 : Set.range q ⊆ Set.range W.ι := by rwa [Scheme.Opens.range_ι]
  have h2 : Set.range g ⊆ Set.range (f ⁻¹ᵁ W).ι := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨w, rfl⟩
    exact hW ⟨w, by rw [← e]; rfl⟩
  have e1 := IsOpenImmersion.lift_fac W.ι q h1
  have e2 := IsOpenImmersion.lift_fac (f ⁻¹ᵁ W).ι g h2
  have : IsOpenImmersion (IsOpenImmersion.lift W.ι q h1 ≫ W.ι) := e1.symm ▸ hq
  have : IsDominant (IsOpenImmersion.lift (f ⁻¹ᵁ W).ι g h2 ≫ (f ⁻¹ᵁ W).ι) := e2.symm ▸ hg
  refine ⟨V, IsOpenImmersion.lift W.ι q h1, IsOpenImmersion.of_comp _ W.ι, IsOpenImmersion.lift (f ⁻¹ᵁ W).ι g h2,
    ⟨v, ?_⟩, IsDominant.of_comp_of_isOpenImmersion _ (f ⁻¹ᵁ W).ι, ?_⟩
  · refine Subtype.ext ?_
    rw [← hv]
    conv_rhs => rw [← e1]
    rfl
  · rw [← cancel_mono W.ι, Category.assoc, morphismRestrict_ι, ← Category.assoc, e2, e, e1]

namespace RatModel

variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {M M' : RatModel o Ω}

theorem IsNm.isIso_morphismRestrict {J : Type} [Finite J] {u : J → Ω} (h' : M'.IsNm u)
    (hn : ∀ z, IsIntegrallyClosed (M.O z)) {f : M'.Z ⟶ M.Z} (hf : M.IsHom M' (AlgHom.id o Ω) f) (W : M.Z.Opens)
    (hW : ∀ z ∈ W, ∃ i, M.Div u i z) : IsIso (f ∣_ W) := by
  have := M.sep
  have : IsSeparated (f ≫ M.s) := hf.inducedModelMorphism_comp_structureMap.symm ▸ M'.sep
  have : IsSeparated f := IsSeparated.of_comp f M.s
  refine isIso_morphismRestrict_of_local_dominant_sections f W fun z hz => ?_
  obtain ⟨i, hi⟩ := hW z hz
  obtain ⟨U, hU, hD, hR⟩ := h'.2 i hi.1
  obtain ⟨V, hV, hzV, hle⟩ :=
    exists_isAffineOpen_mem_and_subset (U := W ⊓ ⟨_, M.isOpen_setOf_div u i⟩) (x := z) ⟨hz, hi⟩
  obtain ⟨g, hg⟩ := exists_hom_of_map_ringOn (φ := AlgHom.id o Ω) hU
    ⟨genericPoint M'.Z, hD ▸ div_genericPoint hi.1⟩ (V := V) ⟨z, hzV⟩
    fun x hx => mem_ringOn.2 fun w hw =>
      Div.map_mem_O_of_isIntegral (M' := M) (φ := AlgHom.id o Ω) (t := u) (i := i) (z := w) (hle hw).2 ((hR x).1 hx)
  have hp := specMap_valMap_fromSpec hV M.pt (M.top_le_preimage_pt ⟨z, hzV⟩)
  have hid : ∀ {Y : Scheme.{0}} (a : Sp Ω ⟶ Y), spMap (AlgHom.id o Ω).toRingHom ≫ a = a := fun a =>
    (congrArg (· ≫ a) (Spec.map_id _)).trans (Category.id_comp _)
  have hdom : IsDominant (Spec.map (valMap M.pt V (M.top_le_preimage_pt ⟨z, hzV⟩)) ≫ g) := by
    rw [hg, hid]
    infer_instance
  refine ⟨_, hV.fromSpec, inferInstance, g, hV.range_fromSpec ▸ hzV, hV.range_fromSpec ▸ fun w hw => (hle hw).1,
    IsDominant.of_comp (Spec.map (valMap M.pt V (M.top_le_preimage_pt ⟨z, hzV⟩))) g, ?_⟩
  refine hom_ext_of_isOpenImmersion (φ := AlgHom.id o Ω) hV.fromSpec hp ?_ (hp.trans (hid _).symm)
  rw [← Category.assoc, hg, hid]
  exact hf

end RatModel

theorem isIso_morphismRestrict_of_isNm_prod : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] (M : RatModel o Ω) (M' : RatModel o Ω) (J J' : Type) [Finite J] [Finite J'] (t : J → Ω) (t' : J' → Ω) (f : M'.Z ⟶ M.Z), M.IsNm t → M'.IsNm (fun q : J × J' => t q.1 * t' q.2) → IsProper M'.s → M.IsHom M' (AlgHom.id o Ω) f → ∀ W : M.Z.Opens, (∀ z ∈ W, ∃ i', M.Div t' i' z) → IsIso (f ∣_ W) := by
  intro o Ω _ _ _ M M' J J' _ _ t t' f h h' _ hf W hW
  refine h'.isIso_morphismRestrict (RatModel.isIntegrallyClosed_O h.isNormalScheme) hf W fun z hz => ?_
  obtain ⟨i, hi⟩ := h.1 z
  obtain ⟨i', hi'⟩ := hW z hz
  exact ⟨(i, i'), RatModel.div_prod_iff.2 ⟨hi, hi'⟩⟩

end GlobalTheory.ZH
end
