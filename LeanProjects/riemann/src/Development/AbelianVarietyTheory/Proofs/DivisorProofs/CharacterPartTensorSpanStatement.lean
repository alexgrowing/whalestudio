import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CharacterPartTensorSpan
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TprodMemTensSpan
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.character_part_tensor_span : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (P Q R S : ℕ) (x : ι → ℚ) (m : ℕ) (T : ⨂[ℂ] _ : ι, Formalism.BasicNotions.TH.Pol P Q R S), T ∈ GlobalTheory.KFixIrr.chiPart ι P Q R S x ⊓ GlobalTheory.KFixIrr.degLE ι P Q R S m → T ∈ Submodule.span ℂ {U | ∃ g : ι → Formalism.BasicNotions.TH.Pol P Q R S, (∀ w, g w ∈ GlobalTheory.KFixIrr.chiOne P Q R S (x w)) ∧ ∑ w, (g w).totalDegree ≤ m ∧ U = PiTensorProduct.tprod ℂ g} := by
  first | exact @GlobalTheory.KFixIrr.mem_span_tprod_chiOne | exact GlobalTheory.KFixIrr.mem_span_tprod_chiOne | (intros; apply GlobalTheory.KFixIrr.mem_span_tprod_chiOne <;> assumption)
