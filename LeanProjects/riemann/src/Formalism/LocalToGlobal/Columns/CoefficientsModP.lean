import Formalism.LocalToGlobal.Columns.CoefficientsModP.FkMapInitMinor
import Formalism.LocalToGlobal.Columns.CoefficientsModP.FkPderivBlockEmbNe
import Formalism.LocalToGlobal.Columns.CoefficientsModP.PairingNondegenerateHolds
import Formalism.LocalToGlobal.Columns.CoefficientsModP.LatticeBasisExistsHolds
import Formalism.LocalToGlobal.Columns.CoefficientsModP.NablaIndependenceHolds
import Formalism.LocalToGlobal.Columns.CoefficientsModP.TauLatticeLatticeHolds
import Formalism.LocalToGlobal.Columns.CoefficientsModP.NablaRoundFreeHolds
import Formalism.LocalToGlobal.Columns.CoefficientsModP.WeTransposeWordTransposeWord
import Formalism.LocalToGlobal.Columns.CoefficientsModP.BaseCh
import Formalism.LocalToGlobal.Columns.CoefficientsModP.PairBDual
import Formalism.LocalToGlobal.Columns.CoefficientsModP.StdDual
import Formalism.LocalToGlobal.Columns.CoefficientsModP.NabDual

namespace Formalism.L2.DIV

theorem fockSTen : FockSTen := fockSymTensor_holds
theorem pairRat : PairRat := pairingRational_holds
theorem actRat : ActRat := actionRational_holds
theorem pairNondeg : PairNondeg := pairingNondegenerate_holds
theorem pairPos : PairPos := pairingPositive_holds
theorem basisAtEx : BasisAtEx := latticeBasisExists_holds
theorem delIndep : DelIndep := deltaIndependence_holds
theorem nabDelFree : NabDelFree := nablaDeltaFree_holds
theorem nabDelLoc : NabDelLoc := nablaDeltaLocal_holds
theorem nabDelLattice : NabDelLattice := nablaDeltaLattice_holds
theorem tauLatLattice : TauLatLattice := tauLatticeLattice_holds
theorem dualFrLattice : DualFrLattice := dualFrameLattice_holds
theorem dualFrHdual : DualFrHdual := dualFrameHdual_holds
theorem tauLatDual : TauLatDual := tauLatticeDual_holds
theorem roundLat : RoundLat := roundLattice_holds
theorem weylEqDualNabla : Formalism.GradedWeylDivisibility.WeylEqDualNabla := weyl_eq_dual_nabla_holds
theorem pairBDualStd : PairBDualStd := pairBDualStd_of weyl_eq_dual_nabla_holds
theorem pairBDualK : PairBDualK := pairBDualK_of pairBDualStd
theorem pairBDual : PairBDual := pairBDual_of pairBDualStd
theorem nabDelDual : NabDelDual := nabDelDual_of nablaDeltaDescent_holds pairBDualK

end Formalism.L2.DIV
