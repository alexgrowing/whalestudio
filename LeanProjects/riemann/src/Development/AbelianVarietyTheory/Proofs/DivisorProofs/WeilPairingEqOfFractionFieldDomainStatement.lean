import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilPairingEqOfFractionFieldDomain
import Development.AbelianVarietyTheory.Definitions.Divisors.GalRigidOfSurjective
import Development.AbelianVarietyTheory.Definitions.Divisors.MinSt5OfMinSt4
import Development.AbelianVarietyTheory.Definitions.Divisors.IsThetaCompact
import Development.AbelianVarietyTheory.Definitions.Divisors.IsNoetherianRingCompletedStalkSiegelFibrePower
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.SiegJoin GlobalTheory.TChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weilPairing_eq_of_fractionField_domain : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (P : PolAV (Sp R)) (W L : Type) [CommRing W] [IsDomain W] [Field L] [Algebra W L] [IsFractionRing W L] (f : R →+* W) (e : Over.mk (spMap ((algebraMap W L).comp f)) ⟶ Over.mk (spMap f)), e.left = spMap (algebraMap W L) → ∀ (n : ℕ) (x y : Over.mk (spMap f) ⟶ P.A), x ^ n = 1 → y ^ n = 1 → ∀ (w : Wˣ), Out.WeilIs P.A P.L n (e ≫ x) (e ≫ y) (unitOn (Units.map (algebraMap W L).toMonoidHom w)) → Out.WeilIs P.A P.L n x y (unitOn w) := by
  first | exact @GlobalTheory.WeilDomain.weilIs_of_fractionField | exact GlobalTheory.WeilDomain.weilIs_of_fractionField | (intros; apply GlobalTheory.WeilDomain.weilIs_of_fractionField <;> assumption)
