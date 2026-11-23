import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareDecompositionOfBaseChangeAlongIdentity
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SubsetSpanBy
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.squareDecomposition_of_baseChange_along_identity : ∀ (F : Type) [CommRing F] (A : Over (Sp F)) [GrpObj A] (L M : LB A.left), L.IsLB → M.IsLB → SqDec ((Over.pullback (spMap (RingHom.id F))).obj A) (L.pull (pullback.fst A.hom (spMap (RingHom.id F)))) (M.pull (pullback.fst A.hom (spMap (RingHom.id F)))) → SqDec A L M := by
  first | exact @GlobalTheory.SqDecIdBC.sqDec_of_baseChange_id | exact GlobalTheory.SqDecIdBC.sqDec_of_baseChange_id | (intros; apply GlobalTheory.SqDecIdBC.sqDec_of_baseChange_id <;> assumption)
