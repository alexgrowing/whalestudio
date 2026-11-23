import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.FormulaCOf
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.LocalFormIntegralOnLattice
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.AbsNormSmallFinite
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.DensJordanL
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.LocGlobInt
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.RowLatEx
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.DualFamilyCounting.OrbitFinR

namespace Formalism.L2.SG.Pf.Cnt

theorem densAll_of_leaves (hF : DualityBasisChange.FrameBasisL) (hη : EtaLocD) : DensAll :=
  densAll_of' local_self_dual_holds (DualityBasisChange.gaPlusDiag_of hF jordan_decomposition_holds)
    (DualityBasisChange.notIntDens_of_steps local_self_dual_holds hF DualityBasisChange.locGlobIntE) (densProdVal_of hη)

variable [Fact Formalism.HermitianLattices.Ext.L3.HermRepUnram] in
theorem formulaC_holds_of (hF : DualityBasisChange.FrameBasisL) (hη : EtaLocD) (hI : CntIsoInv) : Formalism.L2.SG.PoincareAmplitudeLowerBounds.FormulaC :=
  formulaC_of local_self_dual_holds (DualityBasisChange.gaPlusDiag_of hF jordan_decomposition_holds)
    (DualityBasisChange.notIntDens_of_steps local_self_dual_holds hF DualityBasisChange.locGlobIntE) (densProdVal_of hη)
    (densMultInt_of local_self_dual_holds (DualityBasisChange.gaPlusDiag_of hF jordan_decomposition_holds) (densProdVal_of hη))
    (orbitFiniteR_of hI) lattice_exists_holds

end Formalism.L2.SG.Pf.Cnt
