import Mathlib
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.MonicFactorizationConvolutionCancelOfOne
import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.InvariantSubspaceMobiusInverseRecEqOfFinrankLt
open Polynomial GlobalTheory.CuspGL
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.monicFactorizationConvolution_cancel_of_one : ∀ (F : Type) [Field F] (a b m : F[X] → ℂ), m 1 = 1 → (∀ P : F[X], P.Monic → conv a m P = conv b m P) → ∀ P : F[X], P.Monic → a P = b P := by
  first | exact @GlobalTheory.CuspGL.ConvCancel.conv_cancel | exact GlobalTheory.CuspGL.ConvCancel.conv_cancel | (intros; apply GlobalTheory.CuspGL.ConvCancel.conv_cancel <;> assumption)
