import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.DerTail
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.IsMirClass
open Polynomial Formalism.MainNotions.ArithmeticCylinders GlobalTheory.GLq GlobalTheory.GLm
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.der_tail_of_lt_of_le : ∀ (g : ℕ) [Fact g.Prime] (ψ : AddChar (ZMod g) ℂ) (i m n : ℕ) (F : Gn g n → ℂ), i < m → m ≤ n → der ψ i (tail ψ m F) = der ψ i F := by
  first | exact @GlobalTheory.GLm.DerTail.der_tail | exact GlobalTheory.GLm.DerTail.der_tail | (intros; apply GlobalTheory.GLm.DerTail.der_tail <;> assumption)
