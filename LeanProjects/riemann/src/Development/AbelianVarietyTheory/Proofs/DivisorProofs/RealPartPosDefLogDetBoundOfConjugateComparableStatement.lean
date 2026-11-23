import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RealPartPosDefLogDetBoundOfConjugateComparable
import Development.AbelianVarietyTheory.Definitions.Divisors.IsRatioOfWeight
open Filter Topology MeasureTheory GlobalTheory.HSAmp
open scoped ComplexOrder Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.realPart_posDef_logDet_bound_of_conjugate_comparable : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (G : Matrix ι ι ℂ) (κ : ℝ), G.PosDef → 1 ≤ κ → (∀ c : ι → ℂ, (∑ i, ∑ j, (starRingEnd ℂ) (c i) * c j * G i j).re ≤ κ * (∑ i, ∑ j, c i * (starRingEnd ℂ) (c j) * G i j).re) → (G.map Complex.re).PosDef ∧ |Real.log (G.map Complex.re).det - Real.log G.det.re| ≤ Fintype.card ι * Real.log (2 * κ) := by
  first | exact @GlobalTheory.RealPartDet.main | exact GlobalTheory.RealPartDet.main | (intros; apply GlobalTheory.RealPartDet.main <;> assumption)
