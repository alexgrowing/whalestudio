import Mathlib
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.IsAffineHomOfFlatQuotientOfAffineKernel
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory

theorem UpperTheory.isFinite_of_isPullback_fpqc :
    ∀ {X Y X' Y' : Scheme.{0}} (a : X' ⟶ X) (q : X' ⟶ Y') (p : X ⟶ Y) (t : Y' ⟶ Y), IsPullback a q p t → Surjective t → Flat t → QuasiCompact t → IsFinite q → IsFinite p := by
  intro X Y X' Y' a q p t h h₁ h₂ h₃ hq
  have := GlobalTheory.isAffineHom_descendsAlong_fpqc.{0}
  have ht : (@Surjective ⊓ @Flat ⊓ @QuasiCompact : MorphismProperty Scheme.{0}) t :=
    ⟨⟨h₁, h₂⟩, h₃⟩
  have hA : IsAffineHom p :=
    MorphismProperty.of_isPullback_of_descendsAlong (P := @IsAffineHom) h.flip ht inferInstance
  have hU : UniversallyClosed p :=
    MorphismProperty.of_isPullback_of_descendsAlong (P := @UniversallyClosed) h.flip ht inferInstance
  have hL : LocallyOfFiniteType p :=
    MorphismProperty.of_isPullback_of_descendsAlong (P := @LocallyOfFiniteType) h.flip ht inferInstance
  exact (IsFinite.iff_isIntegralHom_and_locallyOfFiniteType _).2
    ⟨IsIntegralHom.iff_universallyClosed_and_isAffineHom.mpr ⟨hU, hA⟩, hL⟩
