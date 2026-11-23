import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilTopGridStageExists
import Development.AbelianVarietyTheory.Definitions.Divisors.RegConst
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta Formalism.L2.DIV IsDedekindDomain NumberField MeasureTheory
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest GlobalTheory.SqTop GlobalTheory.SqTower GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames GlobalTheory.ChainFr GlobalTheory.SquareDict GlobalTheory.SquareComm
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.ConstRatio (Factor)
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weil_top_grid_stage_exists : GlobalTheory.FunPr.Hypotheses₂ →
  GBig fun {D} T _ _ G _ _ _ _ => ∀ (W : G.Weil) (i j : Fin D.R.m), ∃ X : TriG G i j, TopGrid W i j X ∧ IsStageC W i j (pp D j) (qq D j) X := by
  first | exact @GlobalTheory.SqTower.TopGridExists.top_grid_exists | exact GlobalTheory.SqTower.TopGridExists.top_grid_exists | (intros; apply GlobalTheory.SqTower.TopGridExists.top_grid_exists <;> assumption)
