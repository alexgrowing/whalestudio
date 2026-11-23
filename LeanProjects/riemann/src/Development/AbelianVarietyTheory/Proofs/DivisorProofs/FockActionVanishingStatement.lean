import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockActionVanishing
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFockMap
open scoped TensorProduct Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fock_action_vanishing : ∀ (P Q R S : ℕ) (c : ℂ) (f : Formalism.BasicNotions.TH.Pol P Q R S), S < Q → c.re < ((R : ℝ) - S) / 2 →
    (∀ Y : Formalism.BasicNotions.TH.Mat P Q, Formalism.BasicNotions.TH.IsKC Y → Y ∈ Formalism.BasicNotions.TH.upq P Q →
      Formalism.BasicNotions.TH.fockAct1 P Q R S Y f + (c * Y.trace) • f = 0) → f = 0 := by
  first | exact @GlobalTheory.NoFixOne.no_fixed_fock_polynomial | exact GlobalTheory.NoFixOne.no_fixed_fock_polynomial | (intros; apply GlobalTheory.NoFixOne.no_fixed_fock_polynomial <;> assumption)
