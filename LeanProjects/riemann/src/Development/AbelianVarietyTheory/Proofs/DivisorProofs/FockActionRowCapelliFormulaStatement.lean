import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockActionRowCapelliFormula
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EabIsKCInr
open MvPolynomial Formalism.BasicNotions.TH
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fock_action_row_capelli_formula : ∀ (P Q R S : ℕ) (f : Formalism.BasicNotions.TH.Pol P Q R S), (∀ l ∈ f.vars, Formalism.BasicNotions.TH.linePos l = true) → (∀ c d : Fin R, Formalism.BasicNotions.TH.fockAct2 P Q R S (Formalism.BasicNotions.TH.Eab (.inl c) (.inl d)) f = GlobalTheory.Capelli.rowOp ℂ (GlobalTheory.LowIrr.zR P Q R S) c d f + (if c = d then (((P : ℂ) - Q) / 2) else 0) • f) ∧ (∀ c d : Fin S, Formalism.BasicNotions.TH.fockAct2 P Q R S (Formalism.BasicNotions.TH.Eab (.inr c) (.inr d)) f = GlobalTheory.Capelli.rowOp ℂ (GlobalTheory.LowIrr.yS P Q R S) c d f + (if c = d then (((Q : ℂ) - P) / 2) else 0) • f) := by
  first | exact @GlobalTheory.LowIrr.fockAct2_posOnly | exact GlobalTheory.LowIrr.fockAct2_posOnly | (intros; apply GlobalTheory.LowIrr.fockAct2_posOnly <;> assumption)
