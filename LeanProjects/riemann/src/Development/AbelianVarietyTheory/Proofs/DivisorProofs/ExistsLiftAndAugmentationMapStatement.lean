import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLiftAndAugmentationMap
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.RatBasisLinearIndependentInt
open DividedPowers GlobalTheory.Cris GlobalTheory.PDA
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_lift_and_augmentation_map : ∀ (B : Type) [CommRing B] (Q : PDPoly B), (∀ (C : Type) [CommRing C] (f : B →+* C) (c : ℕ → C), c 0 = 1 → (∀ m n, c m * c n = ((m + n).choose m : C) * c (m + n)) → ∃ F : Q.P →+* C, (∀ b, F (algebraMap B Q.P b) = f b) ∧ ∀ n, F (Q.e n) = c n) ∧ ∃ ε : Q.P →ₐ[B] B, ∀ p, p ∈ Q.aug ↔ ε p = 0 := by
  first | exact @GlobalTheory.PDA.PDPoly.exists_lift_and_aug | exact GlobalTheory.PDA.PDPoly.exists_lift_and_aug | (intros; apply GlobalTheory.PDA.PDPoly.exists_lift_and_aug <;> assumption)
