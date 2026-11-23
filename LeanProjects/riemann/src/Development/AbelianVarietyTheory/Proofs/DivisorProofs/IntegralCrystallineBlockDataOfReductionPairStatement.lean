import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralCrystallineBlockDataOfReductionPair
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralBlock
open NumberField GlobalTheory.ExpFrame
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integralCrystallineBlockData_of_reductionPair : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (l : ℕ) [Fact l.Prime] (n t : ℕ) (J : (E →+* PadicAlgCl l) → Fin n → ℤ) (bot : (E →+* PadicAlgCl l) → ℤ), BlockPair E Ω l n t J bot → GlobalTheory.WachBlock.IntegralBlock E Ω l n t J bot := by
  first | exact @GlobalTheory.WachBlock.integralBlock_of_blockPair | exact GlobalTheory.WachBlock.integralBlock_of_blockPair | (intros; apply GlobalTheory.WachBlock.integralBlock_of_blockPair <;> assumption)
