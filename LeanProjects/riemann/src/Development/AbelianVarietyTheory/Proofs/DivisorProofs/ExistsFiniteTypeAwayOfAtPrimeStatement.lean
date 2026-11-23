import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteTypeAwayOfAtPrime
import Development.AbelianVarietyTheory.Definitions.Divisors.SubsetSpanBy
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_finiteType_away_of_finiteType_atPrime : ∀ (R C : Type) [CommRing R] [IsNoetherianRing R] [CommRing C] [IsDomain C] [Algebra R C] (f : R) (𝔭 : Ideal R) [𝔭.IsPrime], algebraMap R C f ≠ 0 → Algebra.FiniteType R (Localization.Away (algebraMap R C f)) → Algebra.FiniteType (Localization.AtPrime 𝔭) (TensorProduct R (Localization.AtPrime 𝔭) C) → ∃ g : R, g ∉ 𝔭 ∧ Algebra.FiniteType R (Localization.Away (algebraMap R C g)) := by
  first | exact @GlobalTheory.Desc.exists_finiteType_away_of_atPrime | exact GlobalTheory.Desc.exists_finiteType_away_of_atPrime | (intros; apply GlobalTheory.Desc.exists_finiteType_away_of_atPrime <;> assumption)
