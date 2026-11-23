import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RamModelDR
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RootLetterInjective
open NumberField MvPolynomial
open Formalism.BasicNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4O GlobalTheory.ShFam GlobalTheory.ShFam.Pad

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.RelabDR

variable {D : D7} (O : Setup D)

def rootSg (x : DV.Rt D.what₂.Tau O.N) : ℤ := if (x.2 : ℕ) < O.j then 1 else -1

abbrev rootL (x : DV.Rt D.what₂.Tau O.N) : Letter O.S.Dw := GlobalTheory.ShFam.Pad.LieGen.rootLetter O.S x

def wholeL (k : Fin (D.R.f * O.N)) : Letter O.S.Dw :=
  (letters O.S.Dw).get (Fin.cast (GlobalTheory.ShFam.Pad.length_letters O.S).symm k)

def ix : GlobalTheory.EigWhole.Var O → Letter O.S.Dw ⊕ Letter O.S.Dw
  | .inl x => .inl (rootL O x)
  | .inr (.inl k) => .inr (wholeL O k)
  | .inr (.inr k) => .inr (wholeL O (Fin.rev k))

def sg : GlobalTheory.EigWhole.Var O → ℤ
  | .inl x => rootSg O x
  | .inr (.inl _) => 1
  | .inr (.inr _) => -1

def rootSub (x : DV.Rt D.what₂.Tau O.N) : MvPolynomial (Letter O.S.Dw) ℝ := C (rootSg O x : ℝ) * X (rootL O x)

end GlobalTheory.RelabDR

end
