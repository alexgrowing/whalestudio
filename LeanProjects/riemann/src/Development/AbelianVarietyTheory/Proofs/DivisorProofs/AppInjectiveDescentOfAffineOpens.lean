import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory.Mum.Glue

theorem app_map {Y Z : Scheme.{0}} (p : Z ⟶ Y) {U V : Y.Opens} (i : U ⟶ V) (a : Γ(Y, V)) :
    (p.app U).hom ((Y.presheaf.map i.op).hom a) =
      (Z.presheaf.map (homOfLE (p.preimage_mono i.le)).op).hom ((p.app V).hom a) := by
  rw [← CommRingCat.comp_apply, p.naturality, CommRingCat.comp_apply]
  rfl

theorem map_map {X : Scheme.{0}} {U V W : X.Opens} (i : V ⟶ U) (j : W ⟶ V) (x : Γ(X, U)) :
    (X.presheaf.map j.op).hom ((X.presheaf.map i.op).hom x) =
      (X.presheaf.map (homOfLE (j.le.trans i.le)).op).hom x := by
  rw [← CommRingCat.comp_apply, ← Functor.map_comp]; rfl

theorem le_iSup_affine (Y : Scheme.{0}) (V : Y.Opens) :
    V ≤ ⨆ U : {U : Y.affineOpens // U.1 ≤ V}, U.1.1 := by
  intro x hx
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, hUV⟩ := Y.isBasis_affineOpens.exists_subset_of_mem_open hx V.isOpen
  exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨⟨U, hU⟩, hUV⟩, hxU⟩

theorem le_iSup_preimage_affine {Y Z : Scheme.{0}} (p : Z ⟶ Y) (V : Y.Opens) :
    p ⁻¹ᵁ V ≤ ⨆ U : {U : Y.affineOpens // U.1 ≤ V}, p ⁻¹ᵁ U.1.1 := by
  intro x hx
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, hUV⟩ := Y.isBasis_affineOpens.exists_subset_of_mem_open hx V.isOpen
  exact TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨⟨U, hU⟩, hUV⟩, hxU⟩

end GlobalTheory.Mum.Glue

namespace GlobalTheory.Mum

theorem app_injective_and_descent_of_affineOpens : ∀ (Y Z : Scheme.{0}) (p : Z ⟶ Y), (∀ V : Y.Opens, IsAffineOpen V → (Function.Injective (p.app V).hom ∧ ∀ f : Γ(Z, p ⁻¹ᵁ V), (∀ h : pullback.snd p p ⁻¹ᵁ (p ⁻¹ᵁ V) = pullback.fst p p ⁻¹ᵁ (p ⁻¹ᵁ V), ((pullback.fst p p).app _).hom f = ((pullback.snd p p).appLE _ _ h.ge).hom f) → f ∈ Set.range (p.app V).hom)) → ∀ V : Y.Opens, (Function.Injective (p.app V).hom ∧ ∀ f : Γ(Z, p ⁻¹ᵁ V), (∀ h : pullback.snd p p ⁻¹ᵁ (p ⁻¹ᵁ V) = pullback.fst p p ⁻¹ᵁ (p ⁻¹ᵁ V), ((pullback.fst p p).app _).hom f = ((pullback.snd p p).appLE _ _ h.ge).hom f) → f ∈ Set.range (p.app V).hom) := by
  intro Y Z p H
  have inj : ∀ W : Y.Opens, Function.Injective (p.app W).hom := by
    intro W a b hab
    refine Y.sheaf.eq_of_locally_eq' (fun U : {U : Y.affineOpens // U.1 ≤ W} ↦ U.1.1) W
      (fun U ↦ homOfLE U.2) (Glue.le_iSup_affine Y W) a b fun U ↦ ?_
    apply (H U.1.1 U.1.2).1
    show (p.app _).hom ((Y.presheaf.map (homOfLE U.2).op).hom a) =
      (p.app _).hom ((Y.presheaf.map (homOfLE U.2).op).hom b)
    rw [Glue.app_map, Glue.app_map, hab]
  intro V
  refine ⟨inj V, fun f hf ↦ ?_⟩
  have hV : pullback.snd p p ⁻¹ᵁ (p ⁻¹ᵁ V) = pullback.fst p p ⁻¹ᵁ (p ⁻¹ᵁ V) := by
    show (pullback.snd p p ≫ p) ⁻¹ᵁ V = (pullback.fst p p ≫ p) ⁻¹ᵁ V
    rw [pullback.condition]
  have hf' := hf hV
  have hU : ∀ U : {U : Y.affineOpens // U.1 ≤ V}, ∃ g : Γ(Y, U.1.1), (p.app U.1.1).hom g =
      (Z.presheaf.map (homOfLE (p.preimage_mono U.2)).op).hom f := by
    intro U
    apply (H U.1.1 U.1.2).2
    intro h'
    rw [Glue.app_map, hf', ← CommRingCat.comp_apply, Scheme.Hom.appLE_map, ← CommRingCat.comp_apply,
      Scheme.Hom.map_appLE]
  choose g hg using hU
  obtain ⟨s, hs, -⟩ := Y.sheaf.existsUnique_gluing' (fun U : {U : Y.affineOpens // U.1 ≤ V} ↦ U.1.1) V
    (fun U ↦ homOfLE U.2) (Glue.le_iSup_affine Y V) g (by
      intro U U'
      apply inj
      show (p.app _).hom ((Y.presheaf.map _).hom (g U)) = (p.app _).hom ((Y.presheaf.map _).hom (g U'))
      rw [Glue.app_map, Glue.app_map, hg, hg, Glue.map_map, Glue.map_map])
  refine ⟨s, ?_⟩
  refine Z.sheaf.eq_of_locally_eq' (fun U : {U : Y.affineOpens // U.1 ≤ V} ↦ p ⁻¹ᵁ U.1.1) (p ⁻¹ᵁ V)
    (fun U ↦ homOfLE (p.preimage_mono U.2)) (Glue.le_iSup_preimage_affine p V) _ _ fun U ↦ ?_
  have e := Glue.app_map p (homOfLE U.2) s
  have hsU : (Y.presheaf.map (homOfLE U.2).op).hom s = g U := hs U
  rw [hsU, hg] at e
  exact e.symm

end GlobalTheory.Mum
