import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.BettiKummerRelationPadicAdd
import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HsCodiscreteNeBot
open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ GlobalTheory.KZ.BettiB
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.bettiKummerRelationPadic_add : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ} (X : Tower Ω ε) (N l : ℕ) [Fact l.Prime] (b b' : X.Fn l) (c c' : Gam N l → MvPolynomial (Fin 2) ℤ_[l]), BtZ X N l b c → BtZ X N l b' c' → BtZ X N l (b + b') (c + c') := by
  first | exact @GlobalTheory.KZ.BettiB.Add.btZ_add | exact GlobalTheory.KZ.BettiB.Add.btZ_add | (intros; apply GlobalTheory.KZ.BettiB.Add.btZ_add <;> assumption)
