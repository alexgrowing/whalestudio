import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DzWedgeDzbarSumPowCardEqFactorialDetProd
import Development.AbelianVarietyTheory.Definitions.Divisors.BsLApply
open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc GlobalTheory.FlagCell2
open GlobalTheory.FlagFibre (Low)
open scoped Matrix ContDiff ComplexOrder ENNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dzWedgeDzbar_sum_pow_card_eq_factorial_det_prod : ∀ (n : ℕ) (B : Type) [Fintype B] [DecidableEq B] (e : B → Fin n), Function.Injective e → ∀ K : Matrix B B ℂ, (∑ a, ∑ b, K a b • sym (e a, e b) : Ev n) ^ Fintype.card B = ((Fintype.card B).factorial * K.det : ℂ) • ∏ a, sym (e a, e a) := by
  first | exact @GlobalTheory.FlagCell2.pow_card_sum_sym | exact GlobalTheory.FlagCell2.pow_card_sum_sym | (intros; apply GlobalTheory.FlagCell2.pow_card_sum_sym <;> assumption)
