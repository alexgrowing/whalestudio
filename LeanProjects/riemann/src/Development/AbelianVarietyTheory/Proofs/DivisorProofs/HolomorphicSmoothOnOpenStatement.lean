import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HolomorphicSmoothOnOpen
import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.SiegelReframe
open Matrix MeasureTheory GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe
open scoped Real ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.holomorphic_smooth_on_open : ∀ {g : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E] {s : Set (Pt E g)} {φ : Pt E g → ℂ}, IsOpen s → DifferentiableOn ℂ φ s → ContDiffOn ℝ ∞ φ s := by
  first | exact @GlobalTheory.contDiffOn_real_of_differentiableOn_pt | exact GlobalTheory.contDiffOn_real_of_differentiableOn_pt | (intros; apply GlobalTheory.contDiffOn_real_of_differentiableOn_pt <;> assumption)
