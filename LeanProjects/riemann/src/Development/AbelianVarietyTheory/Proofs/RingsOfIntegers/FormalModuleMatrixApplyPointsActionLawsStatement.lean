import Mathlib
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.FormalModuleMatrixApplyPointsActionLaws
import Development.AbelianVarietyTheory.Definitions.PlaceAdaptation.AdaptStd
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.PtTie
open ReciprocityTheory.ChartRestriction.G.TB (dAct dLin)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.PlaceInt
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.formalModuleMatrixApplyPoints_action_laws : ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [IsAdicComplete (maximalIdeal V) V] [CharZero V] (d : ℕ) (O : Type) [CommRing O] [StarRing O] (B : FB V d O) (n m : ℕ) (p q : Matrix (Fin n) (Fin n) O) (x y : Fin n → Pt V m d), (∀ b i, MvPowerSeries.constantCoeff (x b i) ∈ maximalIdeal V) → (∀ b i, MvPowerSeries.constantCoeff (y b i) ∈ maximalIdeal V) → (∀ b i, MvPowerSeries.constantCoeff (matV B p x b i) ∈ maximalIdeal V) ∧ matV B (p * q) x = matV B p (matV B q x) ∧ (matV B p (fun b => addV B.G.F (x b) (y b)) = fun b => addV B.G.F (matV B p x b) (matV B p y b)) ∧ (∀ a : O, matV B (a • (1 : Matrix (Fin n) (Fin n) O)) x = fun b => compV (B.A.act a) (x b)) ∧ (∀ b i, evV x (matV B p (fun j => pt V (n := n) d j) b i) = matV B p x b i) ∧ (∀ b i, MvPowerSeries.constantCoeff (matV B p (fun j => pt V (n := n) d j) b i) = 0) ∧ ∀ f : PS V n d, pullM B (p * q) f = pullM B q (pullM B p f) := by
  first | exact @GlobalTheory.PlaceInt.MatAct.matV_laws | exact GlobalTheory.PlaceInt.MatAct.matV_laws | (intros; apply GlobalTheory.PlaceInt.MatAct.matV_laws <;> assumption)
