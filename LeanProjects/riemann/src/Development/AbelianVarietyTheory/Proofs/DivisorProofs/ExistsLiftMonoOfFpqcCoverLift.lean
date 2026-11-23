import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SameIdIff
import Development.AbelianVarietyTheory.Definitions.Divisors.NotIsIsoSpMapDnFst
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon GlobalTheory.DualOpen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.DualOpen

theorem exists_lift_of_fpqc_cover : ∀ (G T T' Y : Scheme.{0}) (π : G ⟶ Y) [Mono π] (y : T ⟶ Y) (t : T' ⟶ T)
    [Flat t] [Surjective t] [QuasiCompact t] (z : T' ⟶ G), z ≫ π = t ≫ y → ∃ w : T ⟶ G, w ≫ π = y := by
  intro G T T' Y π _ y t _ _ _ z hz
  let s := pullback.snd π y
  let σ : T' ⟶ pullback s t :=
    pullback.lift (pullback.lift z t hz) (𝟙 T') (by rw [Category.id_comp]; exact pullback.lift_snd _ _ _)
  have hσ : σ ≫ pullback.snd s t = 𝟙 T' := pullback.lift_snd _ _ _
  haveI : IsSplitEpi (pullback.snd s t) := ⟨⟨⟨σ, hσ⟩⟩⟩
  haveI : IsIso (pullback.snd s t) := isIso_of_mono_of_isSplitEpi _
  have hq : (@Surjective ⊓ @Flat ⊓ @QuasiCompact : MorphismProperty Scheme.{0}) t :=
    ⟨⟨‹_›, ‹_›⟩, ‹_›⟩
  have hs : IsIso s :=
    MorphismProperty.of_pullback_snd_of_descendsAlong (P := MorphismProperty.isomorphisms Scheme.{0})
      (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact) hq (MorphismProperty.isomorphisms.infer_property _)
  refine ⟨inv s ≫ pullback.fst π y, ?_⟩
  rw [Category.assoc, pullback.condition, IsIso.inv_hom_id_assoc]

end GlobalTheory.DualOpen
