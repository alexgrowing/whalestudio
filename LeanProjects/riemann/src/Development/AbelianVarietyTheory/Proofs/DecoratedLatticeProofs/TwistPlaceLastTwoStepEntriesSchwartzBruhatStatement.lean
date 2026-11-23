import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TwistPlaceLastTwoStepEntriesSchwartzBruhat
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.CosInj
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.QPl ValuativeRel
open GlobalTheory.PosOne (toOne Covers TriPos)
open GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage (app HasTensorVal fl opEFJ IsQuotIntFJ RFJ)
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (IsCO)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twistPlace_last_two_step_entries_schwartzBruhat : ∀ (D : D7) (c : Comm D) (v : VCom c) χ (Q : QAt v χ) α yb, Q.T.xiPen (box _ Q.c₂) (Q.rep Q.s 0 rfl α) yb ∈ SB _ ∧ Q.T.xiTop (box _ Q.c₂) Q.ψk Q.ν (-1) yb ∈ SB _ := by
  first | exact @GlobalTheory.QPl.LastTwo.entries_mem_SB | exact GlobalTheory.QPl.LastTwo.entries_mem_SB | (intros; apply GlobalTheory.QPl.LastTwo.entries_mem_SB <;> assumption)
