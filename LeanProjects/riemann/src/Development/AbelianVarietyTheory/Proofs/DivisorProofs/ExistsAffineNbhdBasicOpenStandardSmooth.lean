import Development.AbelianVarietyTheory.Definitions.Divisors.SameIdIff
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitsPatch
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option backward.isDefEq.respectTransparency false

noncomputable section
namespace GlobalTheory.Pinch

theorem appTop_ι_comp_eq {C Z : Scheme.{0}} (e : C ⟶ Z) (U : C.Opens) :
    (U.ι ≫ e).appTop = e.appLE ⊤ U le_top ≫ U.topIso.inv := by
  simp only [Scheme.Hom.appLE, Scheme.Opens.topIso, Scheme.Hom.comp_appTop, Scheme.Opens.ι_app]
  simp [← Functor.map_comp]

theorem exists_affine_basicOpen_standardSmooth : ∀ (g : ℕ) (C Z : Scheme.{0}) [IsAffine Z] (e : C ⟶ Z),
    SmoothOfRelativeDimension g e → ∀ x : C, ∃ O : C.Opens, IsAffineOpen O ∧ x ∈ O ∧
      ∀ r : Γ(C, O), (((C.basicOpen r).ι ≫ e).appTop).hom.IsStandardSmoothOfRelativeDimension g := by
  intro g C Z _ e he x
  obtain ⟨_, ⟨W, hW, rfl⟩, hxW, -⟩ := C.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
  have hW : IsAffineOpen W := hW
  have h0 := HasRingHomProperty.appLE (@SmoothOfRelativeDimension g) e he
    ⟨⊤, isAffineOpen_top Z⟩ ⟨W, hW⟩ le_top
  obtain ⟨s, hs, h'⟩ := (RingHom.locally_iff_isLocalization
    RingHom.isStandardSmoothOfRelativeDimension_respectsIso _).1 h0
  have hcov := hW.self_le_iSup_basicOpen_iff.2 hs hxW
  obtain ⟨⟨t, ht⟩, hxt⟩ := TopologicalSpace.Opens.mem_iSup.1 hcov
  have hl := hW.isLocalization_basicOpen t
  have h1 := h' t ht Γ(C, C.basicOpen t)
  refine ⟨C.basicOpen t, hW.basicOpen t, hxt, fun r => ?_⟩
  have hl2 := (hW.basicOpen t).isLocalization_basicOpen r
  have h2 := (RingHom.isStandardSmoothOfRelativeDimension_stableUnderCompositionWithLocalizationAway g).right
    Γ(C, C.basicOpen r) r _ h1
  have h3 : (e.appLE ⊤ (C.basicOpen r) le_top).hom.IsStandardSmoothOfRelativeDimension g := by
    convert h2 using 1
    ext a
    change _ = (C.presheaf.map (homOfLE (C.basicOpen_le r)).op) ((C.presheaf.map (homOfLE (C.basicOpen_le t)).op) _)
    rw [← CommRingCat.comp_apply, ← CommRingCat.comp_apply, Scheme.Hom.appLE_map_assoc, Scheme.Hom.appLE_map]
  rw [appTop_ι_comp_eq, CommRingCat.hom_comp]
  exact RingHom.isStandardSmoothOfRelativeDimension_respectsIso.1 _
    (C.basicOpen r).topIso.symm.commRingCatIsoToRingEquiv h3

end GlobalTheory.Pinch
