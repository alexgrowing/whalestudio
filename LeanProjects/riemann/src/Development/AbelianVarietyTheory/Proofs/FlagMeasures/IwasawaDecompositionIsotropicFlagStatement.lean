import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IwasawaDecompositionIsotropicFlag
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.BlockAnti
open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.iwasawa_decomposition_isotropic_flag : ∀ (k r : ℕ), ∀ g ∈ GG k r, ∃ n ∈ Nset k r, ∃ a : Fin r → ℝ, (∀ b, 0 < a b) ∧ ∃ m ∈ UH (Hb k), ∃ κ ∈ (GG k r ∩ (Matrix.unitaryGroup (Fin (2 * r + k + 1)) ℂ : Set (Mat k r))), g = n * uEmb k r (Matrix.diagonal fun b => (a b : ℂ)) * mEmb k r m * κ := by
  first | exact @GlobalTheory.Amp.Iwa.iwasawa | exact GlobalTheory.Amp.Iwa.iwasawa | (intros; apply GlobalTheory.Amp.Iwa.iwasawa <;> assumption)
