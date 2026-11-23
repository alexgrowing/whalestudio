import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LintegralProductExpChartAllRealPlacesLe
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.ConvolutionSmoothL2
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec
open scoped InnerProductSpace ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lintegral_productExpChart_allRealPlaces_le : ∀ (I : AutInst) (c : InfinitePlace I.F → ℝ) (s : ℝ) (E : InfinitePlace I.F → Fin (I.n ^ 2) → Matrix (Fin I.n) (Fin I.n) ℂ) (Θ : (InfinitePlace I.F → Fin (I.n ^ 2) → ℝ) → I.Ginf), (∀ v, IsGauge (I.ε v) (c v)) → (∀ v i, inG (I.ε v) (E v i)) → (∀ v i j, ((E v i * (E v j)ᴴ).trace).re = if i = j then 1 else 0) → 0 < s → 12 * (I.n : ℝ) ^ 3 * s ≤ 1 → 8 * (I.n : ℝ) ^ 5 * s ≤ 1 → (∀ t v, uMat (Θ t v) = (List.ofFn fun i => NormedSpace.exp ((t v i : ℂ) • E v i)).prod) → ∃ S : Set I.Ginf, MeasurableSet S ∧ (∀ a ∈ S, ∀ a' ∈ S, ∀ v, dOp (uMat ((a * a'⁻¹) v)) ≤ Real.log 2) ∧ ∀ Φ : I.Ginf → ENNReal, Measurable Φ → ∫⁻ t in Set.pi Set.univ (fun _ => Set.pi Set.univ fun _ => Set.Icc (0 : ℝ) s), Φ (Θ t) ≤ ENNReal.ofReal (Real.exp I.f * ∏ v, c v) * ∫⁻ y in S, Φ y ∂(muInf I) := by
  first | exact @GlobalTheory.ProductChartAll.lintegral_chart_all_le | exact GlobalTheory.ProductChartAll.lintegral_chart_all_le | (intros; apply GlobalTheory.ProductChartAll.lintegral_chart_all_le <;> assumption)
