import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PluriharmonicIsRealPartHolomorphic
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.SiegelReframe
open Matrix MeasureTheory GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe
open scoped Real ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pluriharmonic_is_real_part_holomorphic : ∀ {g : ℕ} {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E] {U : Set (Pt E g)} (u : Pt E g → ℝ), IsOpen U → SimplyConnectedSpace U → ContDiffOn ℝ ∞ u U → (∀ P ∈ U, ∀ v w : Pt E g, ddc u P v w = 0) → ∃ F : Pt E g → ℂ, DifferentiableOn ℂ F U ∧ ∀ P ∈ U, (F P).re = u P := by
  first | exact @GlobalTheory.exists_differentiableOn_re_eq_of_ddc_eq_zero | exact GlobalTheory.exists_differentiableOn_re_eq_of_ddc_eq_zero | (intros; apply GlobalTheory.exists_differentiableOn_re_eq_of_ddc_eq_zero <;> assumption)
