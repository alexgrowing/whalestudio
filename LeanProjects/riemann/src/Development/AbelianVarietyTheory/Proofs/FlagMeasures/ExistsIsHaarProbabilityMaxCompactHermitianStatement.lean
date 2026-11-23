import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsIsHaarProbabilityMaxCompactHermitian
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsCompactKH
open MeasureTheory Matrix Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_isHaarProbabilityMaxCompactHermitian : ∀ k r : ℕ, ∃ μ : Measure (Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ), GlobalTheory.KFinAvg.IsHaarKH k r μ := by
  first | exact @GlobalTheory.KFinAvg.exists_isHaarKH | exact GlobalTheory.KFinAvg.exists_isHaarKH | (intros; apply GlobalTheory.KFinAvg.exists_isHaarKH <;> assumption)
