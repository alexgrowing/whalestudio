import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.VolIdxFinP
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.BlkOfOfPtEntry
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.StabilizerLatticeCoordinatesOf
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.LatBAsm
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.CovolOne3CHolds

namespace Formalism.L2.SG.Closed

theorem volume_determined_of_chart (hC : Formalism.L2.SG.NGCut.StabilizerCovolume.ChartC) : Formalism.L2.SG.VolPin.VolumeOddGeneric :=
  Formalism.L2.SG.Pf.VolPinAsm.volume_generic_odd_of_rep Formalism.L2.SG.Pf.VolPinAsm.dictC_holds
    (Formalism.L2.SG.NGCut.StabilizerCovolume.covolOne3C_of hC (Formalism.L2.SG.NGCut.StabilizerCovolume.stabilizerLatticeCoordinates_of Formalism.L2.SG.LatBAsm.stabilizer_lattice_twisted_prod))

theorem volume_determined : Formalism.L2.SG.VolPin.VolumeOddGeneric :=
  Formalism.L2.SG.Pf.VolPinAsm.volume_generic_odd_of_rep Formalism.L2.SG.Pf.VolPinAsm.dictC_holds Formalism.L2.SG.NGCut.StabilizerCovolume.covolOne3C_holds

end Formalism.L2.SG.Closed
