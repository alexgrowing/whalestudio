import Mathlib
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.IsCharacterOverSubfieldInductionIrreducible
import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.AbByPOfComm
open GlobalTheory.BI
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isCharacterOverSubfield_induction_irreducible : ∀ (K L : Type) [Field K] [Field L] [Algebra K L] [CharZero K] [CharZero L] (G : Type) [Group G] [Finite G] (Q : (G → L) → Prop), Q 0 → (∀ φ c : G → L, IsIrrChar K L φ → IsChar K L c → Q c → Q (φ + c)) → ∀ a : G → L, IsChar K L a → Q a := by
  first | exact @GlobalTheory.BI.isChar_induction | exact GlobalTheory.BI.isChar_induction | (intros; apply GlobalTheory.BI.isChar_induction <;> assumption)
