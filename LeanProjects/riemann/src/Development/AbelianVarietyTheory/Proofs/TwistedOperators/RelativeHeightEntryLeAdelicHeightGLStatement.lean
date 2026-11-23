import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RelativeHeightEntryLeAdelicHeightGL
import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.OneLeHtE

open NumberField

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.relativeHeight_entry_le_adelicHeightGL : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (N : ℕ) (γ : GL (Fin N) E) (i j : Fin N), GlobalTheory.RatCount.htE F ((γ : Matrix (Fin N) (Fin N) E) i j) ≤ GlobalTheory.AdelicU.heightGL F (Formalism.UG.bc (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.AF F)) γ) := by
  first | exact @GlobalTheory.RatCount.htE_entry_le_heightGL | exact GlobalTheory.RatCount.htE_entry_le_heightGL | (intros; apply GlobalTheory.RatCount.htE_entry_le_heightGL <;> assumption)
