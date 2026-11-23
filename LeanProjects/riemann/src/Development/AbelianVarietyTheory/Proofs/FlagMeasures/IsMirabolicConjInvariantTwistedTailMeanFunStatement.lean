import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsMirabolicConjInvariantTwistedTailMeanFun
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.IsMirClass
open Polynomial Formalism.MainNotions.ArithmeticCylinders GlobalTheory.GLq GlobalTheory.GLm
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isMirabolicConjInvariant_twistedTailMeanFun : ∀ (g : ℕ) [Fact g.Prime] (ψ : AddChar (ZMod g) ℂ) (m n : ℕ) (F : Gn g n → ℂ), 1 ≤ m → m ≤ n → IsMirClass F → IsMirClass (tail ψ m F) := by
  first | exact @GlobalTheory.GLm.TailClass.isMirClass_tail | exact GlobalTheory.GLm.TailClass.isMirClass_tail | (intros; apply GlobalTheory.GLm.TailClass.isMirClass_tail <;> assumption)
