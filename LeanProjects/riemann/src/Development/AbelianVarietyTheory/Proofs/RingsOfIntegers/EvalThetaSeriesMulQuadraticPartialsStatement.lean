import Mathlib
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.EvalThetaSeriesMulQuadraticPartials
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.SmallPointsSubstitutionAlgHomSinglePoint
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.PtTie
open ReciprocityTheory.ChartRestriction.G.TB (dAct dLin)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.PlaceInt
open GlobalTheory.TransUnit
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eval_thetaSeries_mul_quadratic_partials : ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [IsAdicComplete (maximalIdeal V) V] [CharZero V] (d : ℕ) (O : Type) [CommRing O] [StarRing O] (B : FB V d O) (K : Type) [Field K] [Algebra ℚ K] [Algebra V K] [IsFractionRing V K] (h : PS K 2 d) (w0 : O), B.IsCanonGauge K h → ∀ (p₁ p₂ : (PS V 3 d)ˣ), p₁.val = B.ph1 → p₂.val = B.ph2 → ∀ Θ : PS V 3 d, IsTheta B K h w0 Θ → ∀ (n : ℕ) (x y z : Sm B n), evA ![x, y, z] Θ * (quadQ (u3 p₁) (u3 p₂) (Sm.act B w0) x y z).val = 1 := by
  first | exact @GlobalTheory.TransUnit.evA_theta_mul_quadQ | exact GlobalTheory.TransUnit.evA_theta_mul_quadQ | (intros; apply GlobalTheory.TransUnit.evA_theta_mul_quadQ <;> assumption)
