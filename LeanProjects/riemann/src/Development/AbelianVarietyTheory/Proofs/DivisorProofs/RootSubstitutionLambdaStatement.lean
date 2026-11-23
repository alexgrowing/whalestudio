import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RootSubstitutionLambda
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RootSub
open NumberField MvPolynomial
open Formalism.BasicNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4O GlobalTheory.ShFam GlobalTheory.ShFam.Pad
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.root_substitution_lambda : ∀ (D : D7) (O : Setup D), aeval (GlobalTheory.RelabDR.rootSub O) (lamA D.what₂.Tau O.N O.j) = -∑ z, X z := by
  first | exact @GlobalTheory.RelabDR.aeval_rootSub_lamA | exact GlobalTheory.RelabDR.aeval_rootSub_lamA | (intros; apply GlobalTheory.RelabDR.aeval_rootSub_lamA <;> assumption)
