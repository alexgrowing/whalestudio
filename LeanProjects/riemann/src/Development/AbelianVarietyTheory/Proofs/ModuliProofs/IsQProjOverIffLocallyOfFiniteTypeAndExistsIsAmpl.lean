import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverIffIsProperAndExistsIsAmpleLB

open AlgebraicGeometry CategoryTheory Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory

variable {R : Type} [CommRing R] {X Y : Scheme.{0}}

theorem isQProjOver_iff_locallyOfFiniteType_and_exists_isAmpleLB (s : X ⟶ Sp R) :
    IsQProjOver s ↔ LocallyOfFiniteType s ∧ ∃ L : LB X, IsAmpleLB L := by
  constructor
  · rintro ⟨N, i, hi, hq, rfl⟩
    haveI := hi
    haveI := hq
    haveI : IsProper (PSpace.str R N) :=
      ((isProjOver_iff_isProper_and_exists_isAmpleLB (PSpace.str R N)).1
        ⟨N, 𝟙 _, inferInstance, Category.id_comp _⟩).1
    exact ⟨inferInstance, _, IsAmpleLB.pull_of_isImmersion (isAmpleLB_basic.2.2.2.2.2.2.1 R N) i⟩
  · rintro ⟨hs, L, hL⟩
    haveI := hs
    exact hL.isQProjOver s

theorem isQProjOver_comp_of_isAffineHom (f : Y ⟶ X) [IsAffineHom f] [LocallyOfFiniteType f] {s : X ⟶ Sp R}
    (h : IsQProjOver s) : IsQProjOver (f ≫ s) := by
  obtain ⟨hs, L, hL⟩ := (isQProjOver_iff_locallyOfFiniteType_and_exists_isAmpleLB s).1 h
  haveI := hs
  refine (isQProjOver_iff_locallyOfFiniteType_and_exists_isAmpleLB (f ≫ s)).2 ⟨inferInstance, L.pull f, ?_⟩
  exact isAmpleLB_basic.2.2.1 f inferInstance hL

theorem isQProjOver_comp_of_isFinite (f : Y ⟶ X) [IsFinite f] {s : X ⟶ Sp R}
    (h : IsQProjOver s) : IsQProjOver (f ≫ s) := isQProjOver_comp_of_isAffineHom f h

theorem isQProjOver_of_isPullback {R' : Type} [CommRing R'] {b : R →+* R'} {s : X ⟶ Sp R} {π : Y ⟶ X}
    {s' : Y ⟶ Sp R'} (H : IsPullback π s' s (spMap b)) (h : IsQProjOver s) : IsQProjOver s' := by
  obtain ⟨hs, L, hL⟩ := (isQProjOver_iff_locallyOfFiniteType_and_exists_isAmpleLB s).1 h
  refine (isQProjOver_iff_locallyOfFiniteType_and_exists_isAmpleLB s').2 ⟨?_, L.pull π, ?_⟩
  · exact MorphismProperty.of_isPullback (P := @LocallyOfFiniteType) H hs
  · exact hL.pull_of_isPullback H

theorem isQProjOver_finite_and_baseChange :
    ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (X : Scheme.{0}) (s : X ⟶ Sp R), IsQProjOver s →
      (∀ (Y : Scheme.{0}) (f : Y ⟶ X), IsFinite f → IsQProjOver (f ≫ s)) ∧
        ∀ (R' : Type) [CommRing R'] (b : R →+* R'), IsQProjOver (pullback.snd s (spMap b)) := by
  intro R _ _ X s h
  refine ⟨fun Y f hf => ?_, fun R' _ b => ?_⟩
  · haveI := hf
    exact isQProjOver_comp_of_isFinite f h
  · exact isQProjOver_of_isPullback (IsPullback.of_hasPullback s (spMap b)) h

end GlobalTheory
