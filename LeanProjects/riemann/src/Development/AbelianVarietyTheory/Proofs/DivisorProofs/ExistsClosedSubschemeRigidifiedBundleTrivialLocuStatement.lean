import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsClosedSubschemeRigidifiedBundleTrivialLocu
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGenPullComp
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc GlobalTheory.TrivLocus
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_closedSubscheme_rigidifiedBundle_trivialLocus : ∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (A : Over S) [GrpObj A] (L₀ N : LB A.left), IsAbelianScheme A → L₀.IsLB → Out.RelAmple A L₀ → N.IsLB → Out.Rigidified A N → ∀ x : S, ∃ (U : S.Opens) (Z : Scheme.{0}) (i : Z ⟶ U), x ∈ U ∧ IsClosedImmersion i ∧ ∀ (T : Scheme.{0}) (t : T ⟶ U), TrivCond A N T (t ≫ U.ι) ↔ ∃ z : T ⟶ Z, z ≫ i = t := by
  first | exact @GlobalTheory.TrivLocusLocal.exists_closed_triv_local | exact GlobalTheory.TrivLocusLocal.exists_closed_triv_local | (intros; apply GlobalTheory.TrivLocusLocal.exists_closed_triv_local <;> assumption)
