import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenericPointMapOverRingHomUnique
import Development.AbelianVarietyTheory.Definitions.Divisors.ExtId
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.UT GlobalTheory.Mum.Two
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.TInj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.genericPointMap_over_ringHom_unique : ∀ {R V : Type} [CommRing R] [IsDomain R] [CommRing V] [IsDomain V] (θ : R →+* V) (κ κ' : Sp (FractionRing V) ⟶ Sp (FractionRing R)), κ ≫ jK R = jK V ≫ spMap θ → κ' ≫ jK R = jK V ≫ spMap θ → κ = κ' := by
  first | exact @GlobalTheory.TInj.genPt_map_unique | exact GlobalTheory.TInj.genPt_map_unique | (intros; apply GlobalTheory.TInj.genPt_map_unique <;> assumption)
