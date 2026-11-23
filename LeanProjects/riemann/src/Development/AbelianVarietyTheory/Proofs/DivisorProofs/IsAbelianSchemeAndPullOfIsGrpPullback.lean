import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ToRingActOpOfRingAct
import Development.AbelianVarietyTheory.Definitions.Divisors.NonemptyHomFixRepTrivial
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsProjBySmoothIsProperGeometricallyIntegral
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.PolBaseChangeOfRelAmpleLocal

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Out

namespace GlobalTheory.GrpPullbackPol

theorem isAbelianScheme_and_pull_of_isGrpPullback :
    ∀ (S S' : Scheme.{0}) (f : S' ⟶ S) (A : Over S) [GrpObj A] [IsCommMonObj A] (A' : Over S')
      [GrpObj A'] [IsCommMonObj A'] (φ : A'.left ⟶ A.left) (L : LB A.left),
      IsGrpPullback A' A f φ → IsAbelianScheme A → L.IsLB → Out.Rigidified A L →
        Out.RelAmple A L →
        IsAbelianScheme A' ∧ (L.pull φ).IsLB ∧ Out.Rigidified A' (L.pull φ) ∧
          Out.RelAmple A' (L.pull φ) := by
  intro S S' f A _ _ A' _ _ φ L h hA hL hr ha
  have hp : IsProper A.hom := hA.proper
  refine ⟨⟨inferInstance, ?_, ?_, ?_⟩, pull_isLB hL φ, PolBaseChange.rigidified_pull h hr, ?_⟩
  · exact MorphismProperty.of_isPullback (P := @Smooth) h.1 hA.smooth
  · exact MorphismProperty.of_isPullback (P := @IsProper) h.1 hA.proper
  · exact MorphismProperty.of_isPullback (P := @GeometricallyConnected) h.1 hA.geomConnected
  · exact AmpleBaseChange.relAmple_of_isPullback hL ha h.1

end GlobalTheory.GrpPullbackPol
