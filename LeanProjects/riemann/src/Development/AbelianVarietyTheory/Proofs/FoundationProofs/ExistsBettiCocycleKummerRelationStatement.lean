import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsBettiCocycleKummerRelation
import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HsCodiscreteNeBot
open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ GlobalTheory.KZ.BettiB
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_betti_cocycle_kummer_relation : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε), Function.Injective ε → (∃ φ : ℂ → ℂ, DifferentiableOn ℂ φ Hs ∧ X.an X.jK = (φ : Mero)) → ∀ (N l w : ℕ) [Fact l.Prime], l ≠ 2 → 5 ≤ N → Nat.Coprime N l → Odd w → ∀ b ∈ X.BSet N l w, ∃ c ∈ Z1 N l w, BtZ X N l b c := by
  first | exact @GlobalTheory.KZ.BettiEx.exists_betti_cocycle | exact GlobalTheory.KZ.BettiEx.exists_betti_cocycle | (intros; apply GlobalTheory.KZ.BettiEx.exists_betti_cocycle <;> assumption)
