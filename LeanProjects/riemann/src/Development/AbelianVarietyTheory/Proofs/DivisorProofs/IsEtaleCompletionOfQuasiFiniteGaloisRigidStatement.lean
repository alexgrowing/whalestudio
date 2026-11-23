import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsEtaleCompletionOfQuasiFiniteGaloisRigid
import Development.AbelianVarietyTheory.Definitions.Divisors.GalRigidOfSurjective
import Development.AbelianVarietyTheory.Definitions.Divisors.MinSt5OfMinSt4
import Development.AbelianVarietyTheory.Definitions.Divisors.FromBase
import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.SiegJoin GlobalTheory.Poinc GlobalTheory.TChart
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isEtaleCompletion_of_quasiFinite_galoisRigid : ∀ (O R : Type) [CommRing O] [IsDomain O] [IsLocalRing O] [IsIntegrallyClosed O] [CharZero O] [Algebra.EssFiniteType ℤ O] [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] (f : O →+* R) [IsLocalHom f], IsAdicComplete (maximalIdeal R) R → (∀ p : Ideal R, p.IsPrime → (maximalIdeal O).map f ≤ p → p = maximalIdeal R) → ((residue R).comp f).Finite → ringKrullDim O ≤ ringKrullDim R → GalRigid f → IsEtaleCompletion f ∧ ((residue R).comp f).FormallyUnramified := by
  first | exact @GlobalTheory.QFEtale.isEtaleCompletion_of_galRigid | exact GlobalTheory.QFEtale.isEtaleCompletion_of_galRigid | (intros; apply GlobalTheory.QFEtale.isEtaleCompletion_of_galRigid <;> assumption)
