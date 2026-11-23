import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniquePadicOfFrobeniusEigenAinf
import Development.AbelianVarietyTheory.Definitions.Divisors.GhostFrobenius
open CategoryTheory Opposite Matrix GlobalTheory GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.existsUnique_padic_of_frobenius_eigen_ainf : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ (ε : PreTilt O p) (hε : IsPrimitiveSystem ε), ∀ a : Ainf p O, WittVector.frobenius a = WittVector.frobenius (xi ε) * a → ∃! c : ℤ_[p], ofPadic p O c * Sandwich.mu ε = a := by
  first | exact @GlobalTheory.PDivLat.existsUnique_padic_of_eigen | exact GlobalTheory.PDivLat.existsUnique_padic_of_eigen | (intros; apply GlobalTheory.PDivLat.existsUnique_padic_of_eigen <;> assumption)
