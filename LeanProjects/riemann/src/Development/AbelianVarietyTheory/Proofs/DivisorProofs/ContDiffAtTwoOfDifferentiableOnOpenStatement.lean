import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContDiffAtTwoOfDifferentiableOnOpen
import Mathlib
open Filter Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.contDiffAt_two_of_differentiableOn_open : ∀ {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {f : E → ℂ} {W : Set E} {w : E}, IsOpen W → w ∈ W → DifferentiableOn ℂ f W → ContDiffAt ℂ 2 f w := by
  first | exact @GlobalTheory.HoloNormed.contDiffAt_two_complex | exact GlobalTheory.HoloNormed.contDiffAt_two_complex | (intros; apply GlobalTheory.HoloNormed.contDiffAt_two_complex <;> assumption)
