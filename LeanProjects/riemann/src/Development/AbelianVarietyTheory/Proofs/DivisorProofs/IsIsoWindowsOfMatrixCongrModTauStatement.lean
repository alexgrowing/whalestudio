import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIsoWindowsOfMatrixCongrModTau
import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isIso_windows_of_matrix_congr_mod_tau : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ (ε : PreTilt O p) (hε : IsPrimitiveSystem ε), ∀ F : BFrame ε, ∀ (d k : ℕ) (U U' : Matrix (Fin d ⊕ Fin k) (Fin d ⊕ Fin k) F.B), IsUnit U → IsUnit U' → (∀ i j, F.τ ∣ U i j - U' i j) → IsNil F.θ F.σ (U * blk d k (p : F.B) 1) → ∃ X : Matrix (Fin d ⊕ Fin k) (Fin d ⊕ Fin k) F.B, (∀ i j, F.τ ∣ X i j - (1 : Matrix (Fin d ⊕ Fin k) (Fin d ⊕ Fin k) F.B) i j) ∧ X * (U' * blk d k (p : F.B) 1) = U * blk d k (p : F.B) 1 * X.map F.σ := by
  first | exact @GlobalTheory.WindowIso.window_iso | exact GlobalTheory.WindowIso.window_iso | (intros; apply GlobalTheory.WindowIso.window_iso <;> assumption)
