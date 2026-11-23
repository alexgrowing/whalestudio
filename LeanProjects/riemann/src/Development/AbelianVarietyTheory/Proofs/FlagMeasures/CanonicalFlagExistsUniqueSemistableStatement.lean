import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CanonicalFlagExistsUniqueSemistable
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LayerProd
import Formalism.HarderNarasimhan.ShiftInvariance
open GlobalTheory.Count Formalism.MainNotions.S Formalism.HN Formalism.REAL Matrix NumberField MeasureTheory Finset
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.canonicalFlag_exists_unique_semistable : ∀ (I : AutInst) (x : I.GA), (∃ (a : ℕ) (S : Fin (a + 1) → Submodule (𝓞 I.E) (Fin I.n → I.E)) (τ : Fin a → ℝ), HasFlag I x S τ) ∧ (∀ (a a' : ℕ) (j : Fin a → ℕ) (τ : Fin a → ℝ) (j' : Fin a' → ℕ) (τ' : Fin a' → ℝ), HasType I x j τ → HasType I x j' τ' → ∃ h : a = a', (∀ i, j i = j' (Fin.cast h i)) ∧ ∀ i, τ i = τ' (Fin.cast h i)) ∧ ∀ (a : ℕ) (S : Fin (a + 1) → Submodule (𝓞 I.E) (Fin I.n → I.E)) (τ : Fin a → ℝ), HasFlag I x S τ → (∀ i : Fin a, S i.castSucc = stepLt I x (τ i) ∧ rkK (S i.castSucc) < rkK (S i.succ) ∧ largestSize (bas I) (frm I x) (S i.succ) = τ i ∧ (∀ N, S i.castSucc < N → N ≤ lamX I x → τ i ≤ sizeQ (bas I) (frm I x) N (S i.castSucc)) ∧ ∀ N, S i.castSucc ≤ N → IsSat (Formalism.HermitianLatticesTheory.realize (bas I) (frm I x)) (S i.succ) N → N ≠ S i.succ → sizeQ (bas I) (frm I x) (S i.succ) N ≤ τ i) ∧ (1 ≤ I.n → (a = 0 ↔ 1 / 2 ≤ least I x) ∧ ∀ h : 0 < a, τ ⟨0, h⟩ = least I x) := by
  first | exact @GlobalTheory.PointFlag.flag_spec | exact GlobalTheory.PointFlag.flag_spec | (intros; apply GlobalTheory.PointFlag.flag_spec <;> assumption)
