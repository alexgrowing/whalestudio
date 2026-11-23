import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.WittExtensionHermitianFrames
import Development.AbelianVarietyTheory.Definitions.Foundations.InFrameStabilizer
open GlobalTheory.SgAlg Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.witt_extension_hermitian_frames : ∀ {E : Type} [Field E] (σ : E →+* E), IsQA σ → ∀ {n a : ℕ} (J : Matrix (Fin n) (Fin n) E), IsHermU σ J → ∀ (X X' : Matrix (Fin n) (Fin a) E), Free X → Free X' → pairM σ J X X = pairM σ J X' X' → ∃ g, IsUn σ J g ∧ g * X = X' := by
  first | exact @GlobalTheory.SgAlg.witt_free_field | exact GlobalTheory.SgAlg.witt_free_field | (intros; apply GlobalTheory.SgAlg.witt_free_field <;> assumption)
