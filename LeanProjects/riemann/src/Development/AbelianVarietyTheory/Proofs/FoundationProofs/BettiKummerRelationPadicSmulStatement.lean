import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.BettiKummerRelationPadicSmul
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HsCodiscreteNeBot
open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ GlobalTheory.KZ.BettiB
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.bettiKummerRelationPadic_smul : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ} (X : Tower Ω ε) (N l : ℕ) [Fact l.Prime] (r : ℤ_[l]) (b : X.Fn l) (c : Gam N l → MvPolynomial (Fin 2) ℤ_[l]), BtZ X N l b c → BtZ X N l (r • b) (r • c) := by
  first | exact @GlobalTheory.KZ.BettiB.btZ_smul | exact GlobalTheory.KZ.BettiB.btZ_smul | (intros; apply GlobalTheory.KZ.BettiB.btZ_smul <;> assumption)
