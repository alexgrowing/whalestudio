import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjugateChartDerivative
import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsTypeIsRealConst
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousAndExistsConjChart
open Filter Topology
open GlobalTheory.CxForm
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ComplexConjugate
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.conjugate_chart_derivative : ∀ (n m : ℕ) (G G' : V n → V m) (v : V n), DifferentiableAt ℂ G (GlobalTheory.ConjChart.conjCoord n v) → (G' =ᶠ[𝓝 v] fun w => GlobalTheory.ConjChart.conjCoord m (G (GlobalTheory.ConjChart.conjCoord n w))) → ∀ (b : Fin n) (a : Fin m), fderiv ℂ G' v (GlobalTheory.GoodMetric.coordVec b) a = conj (fderiv ℂ G (GlobalTheory.ConjChart.conjCoord n v) (GlobalTheory.GoodMetric.coordVec b) a) := by
  first | exact @GlobalTheory.ConjDeriv.fderiv_conj_conj_coordVec | exact GlobalTheory.ConjDeriv.fderiv_conj_conj_coordVec | (intros; apply GlobalTheory.ConjDeriv.fderiv_conj_conj_coordVec <;> assumption)
