import Mathlib
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.DetJacobianFormalModuleMatrixEqConstMulUnit
import Development.AbelianVarietyTheory.Definitions.PlaceAdaptation.AdaptStd
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.PtTie
open ReciprocityTheory.ChartRestriction.G.TB (dAct dLin)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.PlaceInt
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.det_jacobian_formal_module_matrix_eq_const_mul_unit : ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [IsAdicComplete (maximalIdeal V) V] [CharZero V] (d : ℕ) (O : Type) [CommRing O] [StarRing O] (B : FB V d O) (n : ℕ) (p : Matrix (Fin n) (Fin n) O), ∃ U : (PS V n d)ˣ, Matrix.det (Matrix.of fun i j : Fin n × Fin d => MvPowerSeries.pderiv V j (matV B p (fun j => pt V (n := n) d j) i.1 i.2)) = MvPowerSeries.C (jacM B p) * (U : PS V n d) := by
  first | exact @GlobalTheory.PlaceInt.MatJac.det_jacobian_matV | exact GlobalTheory.PlaceInt.MatJac.det_jacobian_matV | (intros; apply GlobalTheory.PlaceInt.MatJac.det_jacobian_matV <;> assumption)
