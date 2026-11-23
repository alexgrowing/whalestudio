import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.GradedPieceSizesUnipotentLeviCompactMove
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.IsGaugeAll
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gradedPieceSizes_unipotent_levi_compact_move : ∀ (I : AutInst) (xf : I.Gf) (a : ℕ) (j : Fin a → ℕ), (∀ i, 1 ≤ j i) → ∀ (S : Fin (a + 1) → Submodule (𝓞 I.E) (Fin I.n → I.E)), IsSatFlag I (lamX I (1, xf)) j S → ∀ u m k : I.Ginf, (∀ v, u v ∈ flagN (I.ε v) (flagAt I S v)) → (∀ v, m v ∈ flagM (I.ε v) (flagAt I S v)) → (∀ v, k v ∈ maxK (I.ε v)) → ∀ i : Fin a, Formalism.HN.sizeQ (bas I) (frm I (u * m * k, xf)) (S i.succ) (S i.castSucc) ^ I.f = Formalism.HN.sizeQ (bas I) (frm I (1, xf)) (S i.succ) (S i.castSucc) ^ I.f * ∏ v, locSize j (flagAt I S v) (uMat (m v)) i := by
  first | exact @GlobalTheory.FlagMeas.SizeMove.size_move | exact GlobalTheory.FlagMeas.SizeMove.size_move | (intros; apply GlobalTheory.FlagMeas.SizeMove.size_move <;> assumption)
