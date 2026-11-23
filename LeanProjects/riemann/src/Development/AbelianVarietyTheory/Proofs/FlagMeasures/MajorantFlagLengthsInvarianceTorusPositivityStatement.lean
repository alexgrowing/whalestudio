import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MajorantFlagLengthsInvarianceTorusPositivity
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.BlockAnti
open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.majorant_flag_lengths_invariance_torus_positivity : ∀ (k r : ℕ) (z : (Fin (2 * r + k + 1) → ℂ)), inWb k r z → (∀ x ∈ GG k r, ∀ s ∈ Sset k r z, ∀ κ ∈ (GG k r ∩ (Matrix.unitaryGroup (Fin (2 * r + k + 1)) ℂ : Set (Mat k r))), (∀ a, lA k r z (s * x * κ) a = lA k r z x a) ∧ Sg k r z (s * x * κ) = Sg k r z x) ∧ (∀ (a : Fin r → ℝ), (∀ b, 0 < a b) → ∀ m ∈ UH (Hb k), ∀ b : Fin r, lA k r z (uEmb k r (Matrix.diagonal fun b => (a b : ℂ)) * mEmb k r m) b.castSucc = (a b)⁻¹) ∧ (∀ x, 1 ≤ Sg k r z x ∧ (∀ a, 0 ≤ lA k r z x a ∧ lA k r z x a ≤ Sg k r z x) ∧ (Sg k r z x = 1 ∨ ∃ a, Sg k r z x = lA k r z x a)) := by
  first | exact @GlobalTheory.Amp.LInv.lengths_basic | exact GlobalTheory.Amp.LInv.lengths_basic | (intros; apply GlobalTheory.Amp.LInv.lengths_basic <;> assumption)
