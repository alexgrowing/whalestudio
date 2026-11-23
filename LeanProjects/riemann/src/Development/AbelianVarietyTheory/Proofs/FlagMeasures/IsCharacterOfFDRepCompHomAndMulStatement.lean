import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsCharacterOfFDRepCompHomAndMul
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.IsMirClass
open Polynomial Formalism.MainNotions.ArithmeticCylinders GlobalTheory.GLq GlobalTheory.GLm
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isCharacterOfFDRep_comp_hom_and_mul : (∀ (G M : Type) [Group G] [Group M] (π : G →* M) (χ : M → ℂ), IsChar χ → IsChar (fun x => χ (π x))) ∧ ∀ (G : Type) [Group G] (α β : G → ℂ), IsChar α → IsChar β → IsChar (fun x => α x * β x) := by
  first | exact @GlobalTheory.GLm.isChar_comp_hom_and_mul | exact GlobalTheory.GLm.isChar_comp_hom_and_mul | (intros; apply GlobalTheory.GLm.isChar_comp_hom_and_mul <;> assumption)
