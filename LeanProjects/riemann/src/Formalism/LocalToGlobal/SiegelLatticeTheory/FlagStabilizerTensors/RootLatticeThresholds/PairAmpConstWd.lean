import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.PvalFormExistsRf
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.FibreCountEqHolds
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedVolumeStatements.FullExistsTiedHolds
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedVolumeStatements.LevelSubgroupProperties

noncomputable section

open Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.PackageTie2 Formalism.L2.SG.TermTieOf

namespace Formalism.L2.SG.Pf.KernelOfEmbedding

variable {D : D7} {X : HidaSetting D} {Y : Formalism.L2.SG.Full.Full X}

theorem ooIntAll_of (hWD : Formalism.L2.SG.WuDecay.WuDecay X) (w w' : D.what₂.Word) :
    OOIntAll X w w' (X.Fu w) (X.Fu w') (Y.what₂ w) (Y.what₂ w') :=
  Formalism.L2.SG.Closed.OOIntAllC_outright D X Y w w'
    (Formalism.L2.SG.Closed.FoldOKC_outright D X Y w (Formalism.L2.SG.Closed.level_subgroup_properties X) hWD)
    (Formalism.L2.SG.Closed.FoldOKC_outright D X Y w' (Formalism.L2.SG.Closed.level_subgroup_properties X) hWD)
    (Formalism.L2.SG.Pf.fundExistsC_holds D X Y w w')

variable {hF : FinX Y} (W : WittDat X) (hI : SIso D.s (sOf hF))

theorem pvalForm_holds (hWD : Formalism.L2.SG.WuDecay.WuDecay X) : ∃ A : AmpDat X, PvalForm W hI A :=
  pvalForm_exists_oi W hI (ooIntAll_of hWD) (Formalism.L2.SG.Pf.FibreEq.FibreCountEq_holds hF)

end Formalism.L2.SG.Pf.KernelOfEmbedding
