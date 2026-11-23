import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LowestDegreeComponentIrreducible
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TprodMemTensSpan
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lowest_degree_component_irreducible : ∀ (P Q R S : ℕ) (x : ℚ) (k k' : ℕ), P ≤ R → Q ≤ S → 0 < k → 0 < k' → x - Formalism.BasicNotions.TH.cPair R S = k → x + Formalism.BasicNotions.TH.cPair R S = k' → ∀ N : Submodule ℂ (Formalism.BasicNotions.TH.Pol P Q R S), N ≤ GlobalTheory.KFixIrr.lowOne P Q R S x (P * k + Q * k') → (∀ Z : Formalism.BasicNotions.TH.Mat R S, Formalism.BasicNotions.TH.IsKC Z → ∀ f ∈ N, Formalism.BasicNotions.TH.fockAct2 P Q R S Z f ∈ N) → N = ⊥ ∨ N = GlobalTheory.KFixIrr.lowOne P Q R S x (P * k + Q * k') := by
  first | exact @GlobalTheory.LowIrr.lowOne_irreducible | exact GlobalTheory.LowIrr.lowOne_irreducible | (intros; apply GlobalTheory.LowIrr.lowOne_irreducible <;> assumption)
