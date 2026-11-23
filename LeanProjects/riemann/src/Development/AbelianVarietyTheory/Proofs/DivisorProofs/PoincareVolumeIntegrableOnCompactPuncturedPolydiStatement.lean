import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PoincareVolumeIntegrableOnCompactPuncturedPolydi
import Development.AbelianVarietyTheory.Definitions.Divisors.EndValuedForm11Coeffs
open MeasureTheory Filter Topology GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.GoodTop
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.poincare_volume_integrableOn_compact_punctured_polydisc : ∀ {n : ℕ} (S : Finset (Fin n)) (K : Set (V n)), IsCompact K → (∀ v ∈ K, ∀ a ∈ S, ‖v a‖ ≤ 1 / 2) → IntegrableOn (fun v => ∏ a, (poinWt S v a)⁻¹ ^ 2) K := by
  first | exact @GlobalTheory.GoodTop.integrableOn_poinVol | exact GlobalTheory.GoodTop.integrableOn_poinVol | (intros; apply GlobalTheory.GoodTop.integrableOn_poinVol <;> assumption)
