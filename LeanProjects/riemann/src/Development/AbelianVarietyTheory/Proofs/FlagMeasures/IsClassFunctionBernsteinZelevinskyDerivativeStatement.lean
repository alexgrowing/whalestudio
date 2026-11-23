import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsClassFunctionBernsteinZelevinskyDerivative
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.IsMirClass
open Polynomial Formalism.MainNotions.ArithmeticCylinders GlobalTheory.GLq GlobalTheory.GLm
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isClassFunction_bernsteinZelevinskyDerivative : ∀ (g : ℕ) [Fact g.Prime] (ψ : AddChar (ZMod g) ℂ) (i n : ℕ) (F : Gn g n → ℂ), i < n → IsMirClass F → IsClass (der ψ i F) := by
  first | exact @GlobalTheory.GLm.DerClass.isClass_der | exact GlobalTheory.GLm.DerClass.isClass_der | (intros; apply GlobalTheory.GLm.DerClass.isClass_der <;> assumption)
