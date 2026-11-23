import Mathlib
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.IsCharacterOverSubfieldOfVirtualAndCharacter
import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.AbByPOfComm
open GlobalTheory.BI
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isCharacterOverSubfield_of_virtual_and_character : ∀ (K L : Type) [Field K] [Field L] [Algebra K L] [CharZero K] [CharZero L] (G : Type) [Group G] [Finite G] (χ : G → L), IsChar L L χ → χ ∈ Virt K L G → IsChar K L χ := by
  first | exact @GlobalTheory.BI.isChar_of_isChar_of_mem_virt | exact GlobalTheory.BI.isChar_of_isChar_of_mem_virt | (intros; apply GlobalTheory.BI.isChar_of_isChar_of_mem_virt <;> assumption)
