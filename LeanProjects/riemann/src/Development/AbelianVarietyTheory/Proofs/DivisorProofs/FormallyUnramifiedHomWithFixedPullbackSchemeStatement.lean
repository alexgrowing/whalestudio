import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormallyUnramifiedHomWithFixedPullbackScheme
import Development.AbelianVarietyTheory.Definitions.Divisors.ToRingActOpOfRingAct
import Development.AbelianVarietyTheory.Definitions.Divisors.NonemptyHomFixRepTrivial
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.formallyUnramified_homWithFixedPullback_scheme : ∀ (S : Scheme.{0}) (A B : Over S) [GrpObj A] [IsCommMonObj A] [GrpObj B] [IsCommMonObj B] (L : LB A.left) (M : LB B.left) (R : HomFixRep A B L M), IsAbelianScheme A → IsAbelianScheme B → FormallyUnramified R.π := by
  first | exact @GlobalTheory.EndLoc.formallyUnramified_homFixRep | exact GlobalTheory.EndLoc.formallyUnramified_homFixRep | (intros; apply GlobalTheory.EndLoc.formallyUnramified_homFixRep; all_goals assumption)
