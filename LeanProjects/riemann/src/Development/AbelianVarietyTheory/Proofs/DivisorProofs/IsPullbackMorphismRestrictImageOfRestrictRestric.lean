import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.QuasiCompact
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

namespace GlobalTheory

theorem isPullback_morphismRestrict_image_of_restrict_restrict :
    ∀ (P' X S T : Scheme.{0}) (a : X ⟶ P') (W : P'.Opens) (V : W.toScheme.Opens) (q : X ⟶ S)
      (h : P' ⟶ T) (π : S ⟶ T),
      IsPullback ((a ∣_ W) ∣_ V) (((a ∣_ W) ⁻¹ᵁ V).ι ≫ (a ⁻¹ᵁ W).ι ≫ q) (V.ι ≫ W.ι ≫ h) π →
      IsPullback (a ∣_ (W.ι ''ᵁ V)) ((a ⁻¹ᵁ (W.ι ''ᵁ V)).ι ≫ q) ((W.ι ''ᵁ V).ι ≫ h) π := by
  intro P' X S T a W V q h π H
  have e1hom : ((a ⁻¹ᵁ W).ι.isoImage ((a ∣_ W) ⁻¹ᵁ V) ≪≫
      X.isoOfEq (image_morphismRestrict_preimage a W V)).hom ≫ (a ⁻¹ᵁ (W.ι ''ᵁ V)).ι =
      ((a ∣_ W) ⁻¹ᵁ V).ι ≫ (a ⁻¹ᵁ W).ι := by
    simp only [Iso.trans_hom, Category.assoc, Scheme.isoOfEq_hom_ι, Scheme.Hom.isoImage_hom_ι]
  refine IsPullback.of_iso H
    ((a ⁻¹ᵁ W).ι.isoImage ((a ∣_ W) ⁻¹ᵁ V) ≪≫ X.isoOfEq (image_morphismRestrict_preimage a W V))
    (W.ι.isoImage V) (Iso.refl S) (Iso.refl T) ?_ ?_ ?_ ?_
  · rw [← cancel_mono (W.ι ''ᵁ V).ι]
    simp only [Category.assoc, Scheme.Hom.isoImage_hom_ι, morphismRestrict_ι]
    rw [reassoc_of% e1hom, morphismRestrict_ι_assoc, morphismRestrict_ι]
  · simp only [Iso.refl_hom, Category.comp_id]
    rw [reassoc_of% e1hom]
  · simp only [Iso.refl_hom, Category.comp_id, Scheme.Hom.isoImage_hom_ι_assoc]
  · simp

end GlobalTheory
