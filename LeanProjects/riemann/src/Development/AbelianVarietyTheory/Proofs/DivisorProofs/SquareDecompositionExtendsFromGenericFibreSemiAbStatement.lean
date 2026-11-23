import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareDecompositionExtendsFromGenericFibreSemiAb
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SubsetSpanBy
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.squareDecomposition_extends_from_genericFibre_semiAbelian : ∀ (R' : Type) [CommRing R'] [IsDomain R'] [IsNoetherianRing R'] [IsIntegrallyClosed R'] [IsLocalRing R'] (G : Over (Sp R')) [GrpObj G], IsSemiAbelian G → ∀ (L M : LB G.left), L.IsLB → M.IsLB → SqDec ((Over.pullback (jK R')).obj G) (L.pull (pullback.fst G.hom (jK R'))) (M.pull (pullback.fst G.hom (jK R'))) → SqDec G L M := by
  first | exact @GlobalTheory.GenericDec.sqDec_of_generic | exact GlobalTheory.GenericDec.sqDec_of_generic | (intros; apply GlobalTheory.GenericDec.sqDec_of_generic <;> assumption)
