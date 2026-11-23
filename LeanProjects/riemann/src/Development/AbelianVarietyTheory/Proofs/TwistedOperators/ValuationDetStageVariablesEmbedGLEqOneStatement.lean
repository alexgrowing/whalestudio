import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ValuationDetStageVariablesEmbedGLEqOne
import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.StepLin
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix ValuativeRel GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.ExpansionInvariance GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.RootEx
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.TopLevelInv GlobalTheory.StepLeft Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.valuation_det_stageVariables_embedGL_eq_one : ∀ {k : Type} [Field k] [ValuativeRel k] {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] {c : ℕ} (κ : GL n k), valuation k (gdet κ : k) = 1 → valuation k (stepLin n' (embX c κ).val).det = 1 := by
  first | exact @GlobalTheory.StepLeft.valuation_det_stepLin_embX | exact GlobalTheory.StepLeft.valuation_det_stepLin_embX | (intros; apply GlobalTheory.StepLeft.valuation_det_stepLin_embX <;> assumption)
