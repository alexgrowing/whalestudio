import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.WittFreeTuplesSplitQuadraticEtale
import Development.AbelianVarietyTheory.Definitions.Foundations.InFrameStabilizer
open GlobalTheory.SgAlg Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.witt_free_tuples_split_quadratic_etale : ∀ {E : Type} [CommRing E] (σ : E →+* E), IsQA σ → (∃ e : E, e * e = e ∧ e + σ e = 1 ∧ ∀ x : E, e * x ≠ 0 → ∃ y, e * x * y = e) → ∀ {n a : ℕ} (J : Matrix (Fin n) (Fin n) E), IsHermU σ J → ∀ (X X' : Matrix (Fin n) (Fin a) E), Free X → Free X' → pairM σ J X X = pairM σ J X' X' → ∃ g, IsUn σ J g ∧ g * X = X' := by
  first | exact @GlobalTheory.SgAlg.WittSplit.witt_split | exact GlobalTheory.SgAlg.WittSplit.witt_split | (intros; apply GlobalTheory.SgAlg.WittSplit.witt_split <;> assumption)
