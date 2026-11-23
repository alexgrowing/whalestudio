import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SmallSizeCanonicalFlagPiecesProperties
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.IsProjOnOne
import Formalism.HarderNarasimhan.ShiftInvariance
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec GlobalTheory.Deep Formalism.HN
open scoped InnerProductSpace ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.smallSizeCanonicalFlag_pieces_properties : ∀ (I : AutInst) (x : I.GA) (a : ℕ) (S : Fin (a + 1) → Submodule (𝓞 I.E) (Fin I.n → I.E)) (τ : Fin a → ℝ), HasFlag I x S τ → (∀ i, SatX I x (S i) ∧ SatX I x (perpIn I x (S i)) ∧ S i ≤ perpIn I x (S (Fin.last a)) ∧ perpIn I x (S (Fin.last a)) ≤ perpIn I x (S i) ∧ rkK (perpIn I x (S i)) + rkK (S i) = I.n) ∧ perpIn I x (S 0) = lamX I x ∧ SizesLe I x (perpIn I x (S (Fin.last a))) (S (Fin.last a)) 2 ∧ ∀ i : Fin a, SizesGe I x (S i.succ) (S i.castSucc) (τ i) ∧ SizesLe I x (S i.succ) (S i.castSucc) (τ i) ∧ SizesLe I x (perpIn I x (S i.castSucc)) (perpIn I x (S i.succ)) (τ i)⁻¹ ∧ S i.succ ≠ ⊥ ∧ largestSize (bas I) (frm I x) (S i.succ) ≤ τ i ∧ SizesGe I x (lamX I x) (S i.succ) (if h : (i : ℕ) + 1 < a then τ ⟨i + 1, h⟩ else 1 / 2) := by
  first | exact @GlobalTheory.FlagPieces.flag_pieces | exact GlobalTheory.FlagPieces.flag_pieces | (intros; apply GlobalTheory.FlagPieces.flag_pieces <;> assumption)
