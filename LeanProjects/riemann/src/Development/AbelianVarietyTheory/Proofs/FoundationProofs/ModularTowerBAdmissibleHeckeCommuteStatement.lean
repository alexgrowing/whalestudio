import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ModularTowerBAdmissibleHeckeCommute
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.EigenOfTwoStep
open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.modularTowerB_admissibleHecke_commute : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε), Function.Injective ε → (∃ φ : ℂ → ℂ, DifferentiableOn ℂ φ Hs ∧ X.an X.jK = (φ : Mero)) → ∀ (N l w : ℕ) [Fact l.Prime], l ≠ 2 → 5 ≤ N → Nat.Coprime N l → Odd w → ∀ T T' : Letter, admitted N l T → admitted N l T' → ∀ b ∈ X.B N l w, X.op N l T (X.op N l T' b) = X.op N l T' (X.op N l T b) := by
  first | exact @GlobalTheory.KZ.B_op_comm | exact GlobalTheory.KZ.B_op_comm | (intros; apply GlobalTheory.KZ.B_op_comm <;> assumption)
