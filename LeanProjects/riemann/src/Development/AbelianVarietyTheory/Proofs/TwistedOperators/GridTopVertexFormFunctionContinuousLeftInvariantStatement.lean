import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.GridTopVertexFormFunctionContinuousLeftInvariant
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.StepUnfold
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gridTopVertexFormFunction_continuous_left_invariant : Big fun {D} _ _ _ _ _ _ _ _ _ _ _ ch => ∀ t y, Continuous (formTop ch t y) ∧
    ∀ γ ∈ GQ (ch.G.V (.grid 0 D.R.m)), ∀ g, formTop ch t y (γ * g) = formTop ch t y g := by
  first | exact @GlobalTheory.FormTopAut.formTop_cont_left | exact GlobalTheory.FormTopAut.formTop_cont_left | (intros; apply GlobalTheory.FormTopAut.formTop_cont_left <;> assumption)
