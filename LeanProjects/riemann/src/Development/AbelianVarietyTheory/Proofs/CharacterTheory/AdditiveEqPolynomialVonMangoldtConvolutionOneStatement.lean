import Mathlib
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.AdditiveEqPolynomialVonMangoldtConvolutionOne
import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.InvariantSubspaceMobiusInverseRecEqOfFinrankLt
open Polynomial GlobalTheory.CuspGL
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.additive_eq_polynomialVonMangoldt_convolution_one : ∀ (F : Type) [Field F] (s : F[X] → ℂ), IsAdditive s → (∀ P : F[X], P.Monic → s P = conv (mangoldt s) (fun _ => 1) P) ∧ (∀ (f : F[X]) (m : ℕ), f.Monic → Irreducible f → 0 < m → mangoldt s (f ^ m) = s f) ∧ ∀ P : F[X], (¬ ∃ (f : F[X]) (m : ℕ), f.Monic ∧ Irreducible f ∧ 0 < m ∧ P = f ^ m) → mangoldt s P = 0 := by
  first | exact @GlobalTheory.CuspGL.mangoldt_conv_spec | exact GlobalTheory.CuspGL.mangoldt_conv_spec | (intros; apply GlobalTheory.CuspGL.mangoldt_conv_spec <;> assumption)
