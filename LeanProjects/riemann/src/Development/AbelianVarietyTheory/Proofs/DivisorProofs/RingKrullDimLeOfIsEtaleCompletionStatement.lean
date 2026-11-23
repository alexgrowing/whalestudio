import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RingKrullDimLeOfIsEtaleCompletion
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
theorem _root_.GlobalTheory.T.ringKrullDim_le_of_isEtaleCompletion' : ∀ (O A : Type) [CommRing O] [IsLocalRing O] [IsNoetherianRing O] [CommRing A] [IsLocalRing A] [IsNoetherianRing A] (ψ : O →+* A) [IsLocalHom ψ], IsEtaleCompletion ψ → ringKrullDim A ≤ ringKrullDim O := by
  first | exact @GlobalTheory.ringKrullDim_le_of_isEtaleCompletion | exact GlobalTheory.ringKrullDim_le_of_isEtaleCompletion | (intros; apply GlobalTheory.ringKrullDim_le_of_isEtaleCompletion <;> assumption)
