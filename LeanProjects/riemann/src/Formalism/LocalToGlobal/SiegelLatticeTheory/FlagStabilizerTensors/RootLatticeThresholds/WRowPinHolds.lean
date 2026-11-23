import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.LoopTieOf
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.MemPerpMapFlag

noncomputable section

open scoped Classical
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PackageTie2

namespace Formalism.L2.SG.Pf.WittFlags

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem WRowPin_holds {D : D7} {X : HidaSetting D} {Y : Formalism.L2.SG.Full.Full X} (hF : FinX Y)
    (hI : SIso D.s (sOf hF)) (W : Formalism.L2.SG.TermTieOf.WittDat X) (H : Formalism.L2.SG.TermTieOf.TieHyp W hI)
    (A : Formalism.L2.SG.TermTieOf.AmpDat X) (hV : Formalism.L2.SG.TermTieOf.PvalForm W hI A) :
    Formalism.L2.SG.LoopTieOf.WRowPin hF hI (Formalism.L2.SG.TermTieOf.termTieOf W hI H A hV) := by
  intro u u' p s hs
  have h2 : (Formalism.L2.SG.TermTieOf.tc hI (D.s.pfst p)).lam = s.lam :=
    (congrArg (fun t => t.lam) hs).symm
  show Formalism.MainNotions.S.wRow D (Formalism.L2.SG.TermTieOf.FlagOfWord W u) (Formalism.L2.SG.TermTieOf.lamOf W hI (D.s.pfst p)) = _
  unfold Formalism.L2.SG.TermTieOf.lamOf
  rw [h2]
  exact WRowIso_holds D (W.δ u) (W.isom u) (X.Fu u) s.lam

end Formalism.L2.SG.Pf.WittFlags
