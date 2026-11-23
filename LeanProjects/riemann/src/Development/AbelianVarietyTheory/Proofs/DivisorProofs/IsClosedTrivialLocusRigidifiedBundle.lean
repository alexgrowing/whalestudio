import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ToRingActOpOfRingAct
import Development.AbelianVarietyTheory.Definitions.Divisors.NonemptyHomFixRepTrivial
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGenPullComp
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClosedSubschemeGlueLocalConditionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineBundleTrivialOnPullbackSquaresOfLocalStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsClosedSubschemeRigidifiedBundleTrivialLocuStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc GlobalTheory.TrivLocus
open scoped CategoryTheory.Obj

namespace GlobalTheory.TrivLocus

theorem trivLocus_closed : ∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (A : Over S) [GrpObj A] (L₀ N : LB A.left), IsAbelianScheme A → L₀.IsLB → Out.RelAmple A L₀ → N.IsLB → Out.Rigidified A N → ∃ (Z : Scheme.{0}) (i : Z ⟶ S), IsClosedImmersion i ∧ ∀ (T : Scheme.{0}) (t : T ⟶ S) (A' : Over T) [GrpObj A'] (φ' : A'.left ⟶ A.left), IsGrpPullback A' A t φ' → ((∃ s : (N.pull φ').Gen, s.IsGen) ↔ ∃ z : T ⟶ Z, z ≫ i = t) := by
  intro S _ A _ L₀ N hA hL₀ hamp hN hrig
  obtain ⟨Z, i, hi, hZ⟩ := GlobalTheory.T.closedSubscheme_glue_local_condition S (TrivCond A N) (trivCond_comp A N)
    (GlobalTheory.T.lineBundleTrivialOnPullbackSquares_of_local S A N hA hN hrig) (GlobalTheory.T.exists_closedSubscheme_rigidifiedBundle_trivialLocus S A L₀ N hA hL₀ hamp hN hrig)
  refine ⟨Z, i, hi, fun T t A' _ φ' hP => ?_⟩
  rw [trivCond_iff A N T t A'.left φ' A'.hom hP.1]
  exact hZ T t

end GlobalTheory.TrivLocus
