import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OverTensorIsPullbackOfIsPullbackSquares
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SRelOneOneIff
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.SiegelToroidalIntegral
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZM GlobalTheory.SiegLev GlobalTheory.SiegelTor
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.over_tensor_isPullback_of_isPullback_squares : ∀ {S S' : Scheme.{0}} (s : S' ⟶ S) (A B : Over S') (Y Z : Over S) (j : A.left ⟶ Y.left) (j' : B.left ⟶ Z.left), IsPullback j A.hom Y.hom s → IsPullback j' B.hom Z.hom s → ∃ k : (A ⊗ B).left ⟶ (Y ⊗ Z).left, k ≫ (fst Y Z).left = (fst A B).left ≫ j ∧ k ≫ (snd Y Z).left = (snd A B).left ≫ j' ∧ IsPullback k (A ⊗ B).hom (Y ⊗ Z).hom s := by
  first | exact @GlobalTheory.over_tensor_isPullback_of_isPullback | exact GlobalTheory.over_tensor_isPullback_of_isPullback | (intros; apply GlobalTheory.over_tensor_isPullback_of_isPullback <;> assumption)
