import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TwistPlaceLastTwoLevelIndicesNeZero
import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.CosInj
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.QPl ValuativeRel
open GlobalTheory.PosOne (toOne Covers TriPos)
open GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage (app HasTensorVal fl opEFJ IsQuotIntFJ RFJ)
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (IsCO)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twistPlace_last_two_level_indices_ne_zero : ∀ (D : D7) (c : Comm D) (v : VCom c) (χ : ℕ → (AE D)ˣ →* Circle) (Q : QAt v χ), Q.idx (Q.s + 1) ≠ 0 ∧ Q.idx (Q.s + 1 + 1) ≠ 0 := by
  first | exact @GlobalTheory.QPl.QAt.idx_last_ne_zero | exact GlobalTheory.QPl.QAt.idx_last_ne_zero | (intros; apply GlobalTheory.QPl.QAt.idx_last_ne_zero <;> assumption)
