import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsThetaMapAffineNormalBaseUniversalGenerator
import Development.AbelianVarietyTheory.Definitions.Divisors.SymTupOne
import Development.AbelianVarietyTheory.Statements.TorsionEndomorphisms.EndDeterminedOnTorsion
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.MinSt2
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_thetaMap_affineNormalBase_universalGenerator : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (L : LB G.left) (ρ : LB.Gen (L.pull (eSec G))), L.IsLB → ρ.IsGen → ∀ (g m n : ℕ) (o R : Type) [CommRing o] [CommRing R] [IsDomain R] [IsNoetherianRing R] [IsIntegrallyClosed R] [CharZero R] (β : o →+* R) (x : Sp R ⟶ S) (θ : SecAt G L x), Odd m → 3 ≤ m → IsUnit (m : R) → n + 1 = m ^ (4 * g) → PolFib G L g x → (∀ (K : Type) [Field K] (i : R →+* K), IsGenSec G L _ (SecAt.pull G L θ i)) → ∃ f : Sp R ⟶ PSpace o n, f ≫ PSpace.str o n = spMap β ∧ ThMap G L ρ m x f := by
  first | exact @GlobalTheory.UMin.MapAff.theta_map_aff | exact GlobalTheory.UMin.MapAff.theta_map_aff | (intros; apply GlobalTheory.UMin.MapAff.theta_map_aff <;> assumption)
