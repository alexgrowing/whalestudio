import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CharacterComponentDegreeLowerBound
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TprodMemTensSpan
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.character_component_degree_lower_bound : ∀ (P Q R S : ℕ) (x : ℚ) (k k' : ℕ), x - Formalism.BasicNotions.TH.cPair R S = k → x + Formalism.BasicNotions.TH.cPair R S = k' → ∀ f ∈ GlobalTheory.KFixIrr.chiOne P Q R S x, f ≠ 0 → P * k + Q * k' ≤ f.totalDegree := by
  first | exact @GlobalTheory.FockLowDeg.lowerDeg | exact GlobalTheory.FockLowDeg.lowerDeg | (intros; apply GlobalTheory.FockLowDeg.lowerDeg <;> assumption)
