import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LowIrreducibleKStable
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EabIsKCInr
open MvPolynomial Formalism.BasicNotions.TH
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.low_irreducible_k_stable : ∀ (P Q R S : ℕ) (x : ℚ) (k k' : ℕ), x - Formalism.BasicNotions.TH.cPair R S = k → x + Formalism.BasicNotions.TH.cPair R S = k' → ∀ Z : Formalism.BasicNotions.TH.Mat R S, Formalism.BasicNotions.TH.IsKC Z → ∀ f ∈ GlobalTheory.KFixIrr.lowOne P Q R S x (P * k + Q * k'), Formalism.BasicNotions.TH.fockAct2 P Q R S Z f ∈ GlobalTheory.KFixIrr.lowOne P Q R S x (P * k + Q * k') := by
  first | exact @GlobalTheory.LowStable.lowOne_stable | exact GlobalTheory.LowStable.lowOne_stable | (intros; apply GlobalTheory.LowStable.lowOne_stable <;> assumption)
