import Mathlib
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReductionProperties
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.SmoothPullbackCompatibility
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.FieldBaseChangeCompatibility
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.DivisorRestrictionFieldBaseChange
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.FunctorialPrincipalization
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.IdealBlowupSequence
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.MarkedSequenceOfBlowups
import Development.ResolutionOfSingularities.Foundations.BlowupUniversalProperty
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionOfSingularities
universe u

open CategoryTheory AlgebraicGeometry

namespace FunctorialResolution.EmbeddedResolution

theorem smooth_id :
    ∀ (X : Scheme.{u}), AlgebraicGeometry.Smooth (CategoryTheory.CategoryStruct.id X) := by
  intro X
  infer_instance

theorem surjective_id :
    ∀ (X : Scheme.{u}), AlgebraicGeometry.Surjective (CategoryTheory.CategoryStruct.id X) := by
  intro X
  constructor
  intro x
  exact ⟨x, rfl⟩

theorem comap_comap :
    ∀ (X Y Z : Scheme.{u}) (f : X ⟶ Y) (g : Y ⟶ Z) (I : Z.IdealSheafData),
      (I.comap g).comap f = I.comap (f ≫ g) := by
  intro X Y Z f g I
  simp

theorem comap_ne_top_of_surjective :
    ∀ (X Y : Scheme.{u}) (h : Y ⟶ X) [AlgebraicGeometry.Surjective h] (Z : X.IdealSheafData),
      Z ≠ ⊤ → Z.comap h ≠ ⊤ := by
  intro X Y h hsurj Z hZ
  have hne : (↑Z.support : Set ↥X).Nonempty := by
    rw [Set.nonempty_iff_ne_empty]
    intro he
    exact hZ ((Scheme.IdealSheafData.eq_top_iff_support_eq_empty Z).mpr he)
  obtain ⟨x, hx⟩ := hne
  obtain ⟨y, hy⟩ := hsurj.1 x
  subst hy
  refine (Scheme.IdealSheafData.support_nonempty_iff_ne_top _).mp ⟨y, ?_⟩
  simpa [AlgebraicGeometry.Scheme.IdealSheafData.support_comap] using hx

theorem flat_fieldBaseChangeProjection :
    ∀ (T : MarkedIdealWithBoundary.{u}) (K : Type u) [Field K] (f : T.base →+* K),
      AlgebraicGeometry.Flat (fieldBaseChangeProjection T K f) := by
  intro T K _ f
  have hflat : AlgebraicGeometry.Flat (specMapOfFieldHom T.base K f) := instFlatSpecMapOfFieldHom ..
  exact MorphismProperty.of_isPullback
    ((CategoryTheory.IsPullback.of_hasPullback T.structMap (specMapOfFieldHom T.base K f)).flip)
    hflat

theorem surjective_fieldBaseChangeProjection :
    ∀ (T : MarkedIdealWithBoundary.{u}) (K : Type u) [Field K] (f : T.base →+* K),
      AlgebraicGeometry.Surjective (fieldBaseChangeProjection T K f) := by
  intro T K _ f
  have hsurj : AlgebraicGeometry.Surjective (specMapOfFieldHom T.base K f) :=
    instSurjectiveSpecMapOfFieldHom ..
  exact surjective_snd_of_isPullback_of_surjective T.structMap
    (CategoryTheory.Limits.pullback.snd T.structMap (specMapOfFieldHom T.base K f))
    (specMapOfFieldHom T.base K f) (fieldBaseChangeProjection T K f)
    (CategoryTheory.IsPullback.of_hasPullback T.structMap (specMapOfFieldHom T.base K f)).flip

theorem comap_fieldBaseChangeProjection_ne_top :
    ∀ (T : MarkedIdealWithBoundary.{u}) (K : Type u) [Field K] (f : T.base →+* K)
      (I : T.scheme.IdealSheafData), I ≠ ⊤ → I.comap (fieldBaseChangeProjection T K f) ≠ ⊤ := by
  intro T K _ f I hI
  have : AlgebraicGeometry.Surjective (fieldBaseChangeProjection T K f) :=
    surjective_fieldBaseChangeProjection T K f
  exact comap_ne_top_of_surjective _ _ (fieldBaseChangeProjection T K f) I hI

end FunctorialResolution.EmbeddedResolution
