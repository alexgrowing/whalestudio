import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.BaseNormalFormRealFramesAtRealPlaces
import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.RowsMeanC
open scoped Classical ENNReal Pointwise NNReal
open MeasureTheory Matrix NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full
  Formalism.L2.SG.LocWSOf Formalism.MainNotions.S.Cnt Formalism.L2.SG.KappaOffDiagonal Formalism.MainNotions.LatticeGluingRadicals GlobalTheory.TypeAsm
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.baseNormalForm_realFrames_at_realPlaces : ∀ (D : D7) (large₂ : SizeData₂ D) (X : HidaSetting D) (u : D.what₂.Word) (C : Choice X 1), Std D large₂ →
    ∀ N : GlobalTheory.DegCnt.NF (HV D) D.R.rS, N.F = F0 X u → N.F' = F0 X u → N.j = 0 → N.T = Tu D u → N.ist = X.fY →
      ∀ τ : D.what₂.Tau, GlobalTheory.DegVol.IsFrameOf N D.R.k (embS D τ) (2 * Formalism.HermitianLatticesTheory.vInv D.host.E) (fun _ => 0)
        (phiV C τ) (zB X (C.Qi τ) u τ) (zB X (C.Qi τ) u τ) 1 := by
  first | exact @GlobalTheory.TypeAsm.baseFrame_real | exact GlobalTheory.TypeAsm.baseFrame_real | (intros; apply GlobalTheory.TypeAsm.baseFrame_real <;> assumption)
