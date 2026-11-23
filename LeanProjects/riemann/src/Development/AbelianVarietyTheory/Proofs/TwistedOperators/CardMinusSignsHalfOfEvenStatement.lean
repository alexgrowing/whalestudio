import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CardMinusSignsHalfOfEven
import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ProjExists
import Development.AbelianVarietyTheory.Definitions.Foundations.StrictInterlaceIffDescEnum
open Formalism.L2.Theta
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.card_minus_signs_half_of_even : ∀ {G : GlobalTheory.SignedHC.GridData} {n : ℕ} {lam : Fin (n + 1) → ℝ} {ε : Fin (n + 1) → Bool} {mu : Fin n → ℝ} {ε' : Fin n → Bool}, Even G.m → 0 < G.ga → IsEnum (G.parPi 0) lam ε → IsEnum G.parD0 mu ε' → (Finset.univ.filter fun a => ε a = false).card = G.m / 2 ∧ (Finset.univ.filter fun i => ε' i = false).card = G.m / 2 := by
  first | exact @GlobalTheory.SignedHC.GridData.card_minus_signs_interlacing_parameters | exact GlobalTheory.SignedHC.GridData.card_minus_signs_interlacing_parameters | (intros; apply GlobalTheory.SignedHC.GridData.card_minus_signs_interlacing_parameters <;> assumption)
