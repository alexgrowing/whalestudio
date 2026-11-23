import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DvrDeterminantFrameRank
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsBasisOfBot
open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps GlobalTheory.DetInv Matrix TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dvr_determinant_frame_rank : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O], v.Integers O → ∀ (ε : PreTilt O p), IsPrimitiveRoot (root ε).untilt p → ∀ (Λ : Type) [CommRing Λ] [IsDomain Λ] [IsDiscreteValuationRing Λ] [Algebra ℤ_[p] Λ] [Module.Finite ℤ_[p] Λ] [FaithfulSMul ℤ_[p] Λ], ∀ (N h : ℕ), h = Module.finrank ℤ_[p] Λ * N → ∀ (D : Datum ε h Λ) (τ : Λ →+* O) (a b : ℕ) (x : Fin a → Fin h → C) (w : Fin a → Fin h → C) (n : Fin b → Fin h → C), IsBasisOf C (lieSub C D τ) x → IsBasisOf C (wQuot C D τ) w → IsBasisOf C (alQuot C D τ) n → a = D.lieRank τ ∧ a + b = N ∧ ∀ i, ∃ y : eig C (actH D) τ, bC C D y = x i := by
  first | exact @GlobalTheory.DetInv.lieRank_add_card_and_lift | exact GlobalTheory.DetInv.lieRank_add_card_and_lift | (intros; apply GlobalTheory.DetInv.lieRank_add_card_and_lift <;> assumption)
