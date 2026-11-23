import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSmoothNhdsOfSmoothOverLocalScheme
import Development.AbelianVarietyTheory.Definitions.Divisors.SubsetSpanBy
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_smooth_nhds_of_smooth_over_local_scheme : ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (P : Scheme.{0}) (p : P ⟶ Sp R) (x : Sp R) (V W : P.Opens), W ≤ V → Smooth (Limits.pullback.snd (V.ι ≫ p) ((Sp R).fromSpecStalk x)) → LocallyOfFiniteType (W.ι ≫ p) → ∀ z : P, z ∈ W → (p z).asIdeal ≤ x.asIdeal → ∃ W' : P.Opens, z ∈ W' ∧ W' ≤ W ∧ Smooth (W'.ι ≫ p) := by
  first | exact @GlobalTheory.Desc.exists_smooth_nhds_of_smooth_fromSpecStalk | exact GlobalTheory.Desc.exists_smooth_nhds_of_smooth_fromSpecStalk | (intros; apply GlobalTheory.Desc.exists_smooth_nhds_of_smooth_fromSpecStalk <;> assumption)
