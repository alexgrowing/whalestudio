import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftWeightRhoEntryValues
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftWeightCombinatorialDataULeUZero
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links GlobalTheory.ExpTie GlobalTheory.ExpTie.Lift
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.liftWeightRho_entryValues : ∀ {D : Formalism.BasicNotions.D7} (L : Formalism.BasicNotions.SizeData₂ D) (j : Fin D.R.m) (τ : D.what₂.Tau), Formalism.IndefR.Bridge.IsLamPrime (GlobalTheory.ExpTie.Lift.lamL j τ) ((j : ℕ) + 1) τ → GlobalTheory.ExpTie.Lift.ValsAt L j τ := by
  first | exact @GlobalTheory.ExpTie.Lift.valsAt_of_isLamPrime | exact GlobalTheory.ExpTie.Lift.valsAt_of_isLamPrime | (intros; apply GlobalTheory.ExpTie.Lift.valsAt_of_isLamPrime <;> assumption)
