import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.InterlacedSignedParameters
import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ProjExists
import Development.AbelianVarietyTheory.Definitions.Foundations.StrictInterlaceIffDescEnum
open Formalism.L2.Theta
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.interlaced_signed_parameters : ∀ {G : GlobalTheory.SignedHC.GridData} {n : ℕ} {lam : Fin (n + 1) → ℝ} {ε : Fin (n + 1) → Bool} {mu : Fin n → ℝ} {ε' : Fin n → Bool}, 0 < G.ga → 1 ≤ G.v G.k + G.b 1 → IsEnum (G.parPi 0) lam ε → IsEnum G.parD0 mu ε' → GlobalTheory.SepReal.Interlaced ε lam ε' mu := by
  first | exact @GlobalTheory.SignedHC.GridData.interlaced_pi_zero_and_D0 | exact GlobalTheory.SignedHC.GridData.interlaced_pi_zero_and_D0 | (intros; apply GlobalTheory.SignedHC.GridData.interlaced_pi_zero_and_D0 <;> assumption)
