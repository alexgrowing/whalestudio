import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RingHomFiniteOfQuasiFiniteCompleteLocal
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.GalRigidOfSurjective
import Development.AbelianVarietyTheory.Definitions.Divisors.MinSt5OfMinSt4
import Development.AbelianVarietyTheory.Definitions.Divisors.FromBase
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsExtensionEtaleCompletionToCompleteLocal
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.SiegJoin GlobalTheory.Poinc GlobalTheory.TChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ringHom_finite_of_quasiFinite_complete_local : ∀ (A R : Type) [CommRing A] [IsLocalRing A] [IsNoetherianRing A] [CommRing R] [IsLocalRing R] [IsNoetherianRing R] (b : A →+* R) [IsLocalHom b], IsAdicComplete (maximalIdeal A) A → (∀ p : Ideal R, p.IsPrime → (maximalIdeal A).map b ≤ p → p = maximalIdeal R) → ((residue R).comp b).Finite → b.Finite := by
  first | exact @GlobalTheory.QuasiFiniteLocal.finite_of_quasiFinite | exact GlobalTheory.QuasiFiniteLocal.finite_of_quasiFinite | (intros; apply GlobalTheory.QuasiFiniteLocal.finite_of_quasiFinite <;> assumption)
