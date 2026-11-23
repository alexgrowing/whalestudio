import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.EndValuedForm11Coeffs
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsOpenOffCoordinateHyperplanes
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PoincareVolumeIntegrableOnCompactPuncturedPolydiStatement

open MeasureTheory Filter Topology GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.GoodTop
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff Matrix

namespace GlobalTheory.GoodTop

theorem integrableOn_offHyp_of_norm_le_poin {n : ℕ} (S : Finset (Fin n)) (U K : Set (V n)) (g : V n → ℂ) (C : ℝ)
    (hU : IsOpen U) (hK : IsCompact K) (hKU : K ⊆ U) (hs : ∀ v ∈ U, ∀ a ∈ S, ‖v a‖ ≤ 1 / 2)
    (hg : ContinuousOn g (offHyp S U)) (h0 : ∀ v ∈ offHyp S U, v ∉ K → g v = 0)
    (hb : ∀ v ∈ offHyp S U, v ∈ K → ‖g v‖ ≤ C * ∏ a, (poinWt S v a)⁻¹ ^ 2) :
    IntegrableOn g (offHyp S U) := by
  have hO : MeasurableSet (offHyp S U) := (isOpen_offHyp_of_isOpen S U hU).measurableSet
  have hv : IntegrableOn (fun v => C * ∏ a, (poinWt S v a)⁻¹ ^ 2) K :=
    (GlobalTheory.T.poincare_volume_integrableOn_compact_punctured_polydisc S K hK fun v hv => hs v (hKU hv)).const_mul C
  have hi : Integrable (K.indicator fun v => C * ∏ a, (poinWt S v a)⁻¹ ^ 2) :=
    (integrable_indicator_iff hK.measurableSet).2 hv
  refine Integrable.mono' hi.integrableOn (hg.aestronglyMeasurable hO) ?_
  refine (ae_restrict_iff' hO).2 (Eventually.of_forall fun v hvO => ?_)
  by_cases hvK : v ∈ K
  · rw [Set.indicator_of_mem hvK]
    exact hb v hvO hvK
  · rw [Set.indicator_of_notMem hvK, h0 v hvO hvK, norm_zero]

end GlobalTheory.GoodTop
