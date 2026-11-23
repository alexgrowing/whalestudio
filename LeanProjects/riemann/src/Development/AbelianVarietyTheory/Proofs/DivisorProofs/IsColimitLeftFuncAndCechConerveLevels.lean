import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC

namespace GlobalTheory.EtC

theorem isColimit_leftFunc_and_cechConerve_levels :
    ∀ (J : Type) [SmallCategory J] (D : J ⥤ Arrow CommRingCat.{0}) (c : Cocone D), IsColimit c →
      Nonempty (IsColimit (Arrow.leftFunc.mapCocone c)) ∧
      ∀ k : SimplexCategory, Nonempty (IsColimit ((CosimplicialObject.cechConerve ⋙
        (evaluation SimplexCategory CommRingCat.{0}).obj k).mapCocone c)) := by
  intro J _ D c hc
  refine ⟨⟨isColimitOfPreserves Arrow.leftFunc hc⟩, fun k => ⟨?_⟩⟩
  have e : (CosimplicialObject.cechConerve ⋙ (evaluation SimplexCategory CommRingCat.{0}).obj k) =
      CosimplicialObject.augmentedCechConerve ⋙ CosimplicialObject.Augmented.drop ⋙
        (evaluation SimplexCategory CommRingCat.{0}).obj k := rfl
  rw [e]
  have h1 : PreservesColimitsOfSize.{0, 0} (CosimplicialObject.augmentedCechConerve (C := CommRingCat.{0})) :=
    CosimplicialObject.cechConerveAdjunction.leftAdjoint_preservesColimits
  have h0 : PreservesColimitsOfShape J (CosimplicialObject.const CommRingCat.{0}) :=
    preservesColimitsOfShape_of_evaluation _ J fun m => by
      have : PreservesColimitsOfShape J (𝟭 CommRingCat.{0}) := inferInstance
      exact this
  have h2 : PreservesColimitsOfShape J (CosimplicialObject.Augmented.drop (C := CommRingCat.{0})) :=
    Comma.preservesColimitsOfShape_snd
  have h3 : PreservesColimitsOfShape J ((evaluation SimplexCategory CommRingCat.{0}).obj k) := inferInstance
  exact @isColimitOfPreserves _ _ _ _ _ _ _ ((evaluation SimplexCategory CommRingCat.{0}).obj k) _
    (isColimitOfPreserves CosimplicialObject.Augmented.drop
      (isColimitOfPreserves CosimplicialObject.augmentedCechConerve hc)) h3.preservesColimit

end GlobalTheory.EtC
