import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ToRingActOpOfRingAct
import Development.AbelianVarietyTheory.Definitions.Divisors.NonemptyHomFixRepTrivial
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBPull
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj

namespace GlobalTheory.TrivLocus

def TrivCond {S : Scheme.{0}} (A : Over S) (N : LB A.left) (T : Scheme.{0}) (t : T ⟶ S) : Prop :=
  ∀ (Y : Scheme.{0}) (φ : Y ⟶ A.left) (y : Y ⟶ T), IsPullback φ y A.hom t →
    ∃ s : (N.pull φ).Gen, s.IsGen

theorem exists_gen_pull_comp {X Y Y' : Scheme.{0}} (N : LB X) (φ : Y ⟶ X)
    (h : Y' ⟶ Y) (hs : ∃ s : (N.pull φ).Gen, s.IsGen) : ∃ s : (N.pull (h ≫ φ)).Gen, s.IsGen := by
  obtain ⟨s, hs⟩ := hs
  exact ⟨LB.pullGen N (fun _ => φ) (fun _ => 1) s h, ReciprocityTheory.ChartRestriction.G.DVR.pullGen_isGen N _ _ s hs h⟩

theorem trivCond_comp {S : Scheme.{0}} (A : Over S) (N : LB A.left) (T T' : Scheme.{0}) (t : T ⟶ S)
    (u : T' ⟶ T) (h : TrivCond A N T t) : TrivCond A N T' (u ≫ t) := by
  intro Y φ y hY
  have hw : φ ≫ A.hom = (y ≫ u) ≫ t := by rw [hY.w, Category.assoc]
  have := exists_gen_pull_comp N _ (pullback.lift φ (y ≫ u) hw)
    (h _ _ _ (IsPullback.of_hasPullback A.hom t))
  rwa [pullback.lift_fst] at this

theorem trivCond_iff {S : Scheme.{0}} (A : Over S) (N : LB A.left) (T : Scheme.{0}) (t : T ⟶ S)
    (X : Scheme.{0}) (φ' : X ⟶ A.left) (x : X ⟶ T) (hP : IsPullback φ' x A.hom t) :
    (∃ s : (N.pull φ').Gen, s.IsGen) ↔ TrivCond A N T t := by
  refine ⟨fun h Y φ y hY => ?_, fun h => h _ _ _ hP⟩
  have := exists_gen_pull_comp N φ' (hP.lift φ y hY.w) h
  rwa [hP.lift_fst] at this

end GlobalTheory.TrivLocus
