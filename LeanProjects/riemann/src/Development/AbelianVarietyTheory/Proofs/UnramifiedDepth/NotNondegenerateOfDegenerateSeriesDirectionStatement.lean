import Mathlib
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.NotNondegenerateOfDegenerateSeriesDirection
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.CubWeilOfInjective
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS ev pt addOf)
open ReciprocityTheory.PGsh.Be2 (nEval)
open GlobalTheory.UU (CubWeil)
attribute [local instance] Over.cartesianMonoidalCategory
open Formalism.L2.FormalSeriesBounds IsLocalRing GlobalTheory.AlphaPair
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.not_nondegenerate_of_degenerate_series_direction : ∀ (Ω : Type) [Field Ω] (p : ℕ) [Fact p.Prime] [CharP Ω p] (S : Scheme.{0}) (s : Sp Ω ⟶ S) (G : Over S) [GrpObj G] [IsCommMonObj G] (L : RigLB G) (c : CubicalStr G L) (d : ℕ) (F : Fin d → PS Ω 2 d) (ph1 ph2 : PS Ω 3 d) (P : PtFam s G d), (∀ j, MvPowerSeries.constantCoeff (F j) = 0) → ev (n := 2) ![0, pt Ω d 0, pt Ω d 1] ph1 = 1 → ev (n := 2) ![pt Ω d 0, 0, pt Ω d 1] ph1 = 1 → ev (n := 2) ![0, pt Ω d 0, pt Ω d 1] ph2 = 1 → IsPtLaw s G F P → IsPtUniv s G P → IsPtCube s G c F ph1 ph2 P → Degenerate p F ph2 → ¬ NonDeg p s G c := by
  first | exact @GlobalTheory.AlphaPair.DegenDir.not_nonDeg_of_degenerate | exact GlobalTheory.AlphaPair.DegenDir.not_nonDeg_of_degenerate | (intros; apply GlobalTheory.AlphaPair.DegenDir.not_nonDeg_of_degenerate <;> assumption)
