import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.LocalDoubleCoset
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.RMeasP

noncomputable section

open scoped Classical
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.PackageTie2
  Formalism.L2.SG.LocWSOf

namespace Formalism.L2.SG.Pf.AmpWinRX

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {X : HidaSetting D} {Y : Full X} {hF : FinX Y} (hI : SIso D.s (sOf hF)) {θ : ℝ} (C : Choice X θ)
  (u u' : D.what₂.Word)

theorem goodW_all (τ : D.what₂.Tau) : GoodW D τ u u' θ (locW C u u' τ) :=
  goodW_of C u u' τ (Formalism.L2.SG.Pf.colsTypeTr C u τ) (Formalism.L2.SG.Pf.colsTypeTr C u' τ) (Formalism.L2.SG.Pf.zTr C u τ)
    (Formalism.L2.SG.Pf.zTr C u' τ) (Formalism.L2.SG.Pf.haarTr C τ)

end Formalism.L2.SG.Pf.AmpWinRX
