import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ToRingActOpOfRingAct
import Development.AbelianVarietyTheory.Definitions.Divisors.NonemptyHomFixRepTrivial
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CharChPartZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FirstCohomologyVanishesOfIsRelAcyclic
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory

theorem GlobalTheory.CxForm.firstCohomologyVanishes_of_isRelAcyclic_affine : ∀ (R : Type) [CommRing R] (X : Scheme.{0}) (f : X ⟶ Spec (CommRingCat.of R)) (M : LB X), M.IsLB → CompactSpace X → GlobalTheory.CxForm.IsRelAcyclic f f M → GlobalTheory.AbLaw.FirstCohomologyVanishes M := by
  first
  | exact @_root_.GlobalTheory.ExactCoboundaryTriple.firstCohomologyVanishes_of_isRelAcyclic
  | exact _root_.GlobalTheory.ExactCoboundaryTriple.firstCohomologyVanishes_of_isRelAcyclic
  | (apply _root_.GlobalTheory.ExactCoboundaryTriple.firstCohomologyVanishes_of_isRelAcyclic <;> assumption)
  | (intros; apply _root_.GlobalTheory.ExactCoboundaryTriple.firstCohomologyVanishes_of_isRelAcyclic <;> assumption)
  | (intros; apply @_root_.GlobalTheory.ExactCoboundaryTriple.firstCohomologyVanishes_of_isRelAcyclic <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.ExactCoboundaryTriple.firstCohomologyVanishes_of_isRelAcyclic ..)
