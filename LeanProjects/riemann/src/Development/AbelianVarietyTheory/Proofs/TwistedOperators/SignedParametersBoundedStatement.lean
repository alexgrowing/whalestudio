import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SignedParametersBounded
import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ProjExists
import Development.AbelianVarietyTheory.Definitions.Foundations.StrictInterlaceIffDescEnum
open Formalism.L2.Theta
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.signed_parameters_bounded : ∀ {G : GlobalTheory.SignedHC.GridData} {n : ℕ} {lam : Fin (n + 1) → ℝ} {ε : Fin (n + 1) → Bool} {mu : Fin n → ℝ} {ε' : Fin n → Bool} {B : ℝ}, 0 ≤ G.v G.k → 0 < G.b 1 → ((G.a 0 : ℚ) : ℝ) ≤ B → (G.b G.m : ℝ) ≤ B → IsEnum (G.parPi 0) lam ε → IsEnum G.parD0 mu ε' → (∀ a, |lam a| ≤ B) ∧ ∀ i, |mu i| ≤ B := by
  first | exact @GlobalTheory.Twist.parPi_parD0_entries_bounded | exact GlobalTheory.Twist.parPi_parD0_entries_bounded | (intros; apply GlobalTheory.Twist.parPi_parD0_entries_bounded <;> assumption)
