import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TrivialLocusLocalToGlobal
import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.LeftZeroDuality.H1StructureDimLe
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsPowMulOfAway
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual PositivityTheory.ObstructionTrivialLocus GlobalTheory.CompanionTheory.TrivLoc
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.trivial_locus_local_to_global : ∀ (S : Scheme.{0}) (A Y : Over S) [GrpObj A], IsAbelianScheme A → ∀ N : LB (A ⊗ Y).left, N.IsLB →
    Triv (ev N (1 : Y ⟶ A) (𝟙 Y)) → ∀ (T : Scheme.{0}) (t : T ⟶ Y.left),
    (∀ x : T, ∃ W : T.Opens, x ∈ W ∧ Locus N (W.ι ≫ t)) → Locus N t := by
  first | exact @GlobalTheory.CompanionTheory.TrivLoc.locus_of_locally | exact GlobalTheory.CompanionTheory.TrivLoc.locus_of_locally | (intros; apply GlobalTheory.CompanionTheory.TrivLoc.locus_of_locally <;> assumption)
