import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.WhittakerCovolume.GenDictXOf
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.SplitStab
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.IsLatRepL
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKwhitCutX
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKwhitDictAsm
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKwhitCell
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKwhitRelEx
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKwhitHeight
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKwhitMeas
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.ThGramIncMK
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.LiftedSchrodingerDatum
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilDatumProperties
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKwhitIwaX
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKwhitVac
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKwhitLinX
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKwhitCoreX
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKwhitPure

set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
namespace PositivityTheory.SiegelWeilFormula.KWhit
open PositivityTheory.SiegelWeilFormula
theorem genDictX_of_k : _root_.PositivityTheory.SiegelWeilFormula.KWhit.GenDictX_k :=
  _root_.PositivityTheory.SiegelWeilFormula.KWhit.dictAsmX_k _root_.PositivityTheory.SiegelWeilFormula.KWhit.cellFormula_k _root_.PositivityTheory.SiegelWeilFormula.KWhit.relEx_k _root_.PositivityTheory.SiegelWeilFormula.KWhit.Ht.heightDict_k _root_.PositivityTheory.SiegelWeilFormula.KWhit.measDict_k _root_.PositivityTheory.SiegelWeilFormula.KWhit.thetaDict_k
theorem whitK_of_k (hT : _root_.PositivityTheory.SiegelWeilFormula.TAll_k) (hA : _root_.PositivityTheory.SiegelWeilFormula.SiegelWeilDatumProperties) (hR : _root_.PositivityTheory.SiegelWeilFormula.RDEx_k) (hF : _root_.PositivityTheory.SiegelWeilFormula.FockMem_k) (hK : _root_.PositivityTheory.SiegelWeilFormula.KFinPoly_k) (hS : _root_.PositivityTheory.SiegelWeilFormula.SecK_k) (hU : _root_.PositivityTheory.SiegelWeilFormula.Unfold_k) (hW : Gen.WhitGenLt)
    (hTC : _root_.PositivityTheory.SiegelWeilFormula.ThetaCoef_k) (hLB : _root_.PositivityTheory.SiegelWeilFormula.LamBd_k) (hPK : _root_.PositivityTheory.SiegelWeilFormula.PolyKFin_k) : _root_.PositivityTheory.SiegelWeilFormula.WhitK_k :=
  _root_.PositivityTheory.SiegelWeilFormula.KWhit.whitK_of_X_k _root_.PositivityTheory.SiegelWeilFormula.KWhit.iwaRedC_k _root_.PositivityTheory.SiegelWeilFormula.KWhit.pureSpan_k _root_.PositivityTheory.SiegelWeilFormula.KWhit.linRedC_k _root_.PositivityTheory.SiegelWeilFormula.KWhit.coreX_k _root_.PositivityTheory.SiegelWeilFormula.KWhit.genDictX_of_k _root_.PositivityTheory.SiegelWeilFormula.KWhit.kFinK_k hT hA hR hF hK hS hU hW hTC hLB hPK
theorem whitEq_of_k (hT : _root_.PositivityTheory.SiegelWeilFormula.TAll_k) (hA : _root_.PositivityTheory.SiegelWeilFormula.SiegelWeilDatumProperties) (hR : _root_.PositivityTheory.SiegelWeilFormula.RDEx_k) (hF : _root_.PositivityTheory.SiegelWeilFormula.FockMem_k) (hK : _root_.PositivityTheory.SiegelWeilFormula.KFinPoly_k) (hS : _root_.PositivityTheory.SiegelWeilFormula.SecK_k) (hU : _root_.PositivityTheory.SiegelWeilFormula.Unfold_k) (hEW : _root_.PositivityTheory.SiegelWeilFormula.EisWk_k)
    (hW : Gen.WhitGenEq) (hTC : _root_.PositivityTheory.SiegelWeilFormula.ThetaCoef_k) (hLB : _root_.PositivityTheory.SiegelWeilFormula.LamBd_k) (hPK : _root_.PositivityTheory.SiegelWeilFormula.PolyKFin_k) : _root_.PositivityTheory.SiegelWeilFormula.WhitEq_k :=
  _root_.PositivityTheory.SiegelWeilFormula.KWhit.whitEq_of_X_k _root_.PositivityTheory.SiegelWeilFormula.KWhit.iwaRedC_k _root_.PositivityTheory.SiegelWeilFormula.KWhit.pureSpan_k _root_.PositivityTheory.SiegelWeilFormula.KWhit.linRedC_k _root_.PositivityTheory.SiegelWeilFormula.KWhit.coreX_k _root_.PositivityTheory.SiegelWeilFormula.KWhit.genDictX_of_k _root_.PositivityTheory.SiegelWeilFormula.KWhit.kFinK_k hT hA hR hF hK hS hU hEW hW hTC hLB hPK
theorem whitLow_of_k (hVK : _root_.PositivityTheory.SiegelWeilFormula.VacK_k)
    (hT : _root_.PositivityTheory.SiegelWeilFormula.TAll_k) (hA : _root_.PositivityTheory.SiegelWeilFormula.SiegelWeilDatumProperties) (hF : _root_.PositivityTheory.SiegelWeilFormula.FockMem_k) (hS : _root_.PositivityTheory.SiegelWeilFormula.SecK_k) (hU : _root_.PositivityTheory.SiegelWeilFormula.Unfold_k) (hEW : _root_.PositivityTheory.SiegelWeilFormula.EisWk_k) (hW : Gen.WhitGenLow)
    (hTC : _root_.PositivityTheory.SiegelWeilFormula.ThetaCoef_k) (hLB : _root_.PositivityTheory.SiegelWeilFormula.LamBd_k) (hPK : _root_.PositivityTheory.SiegelWeilFormula.PolyKFin_k) : _root_.PositivityTheory.SiegelWeilFormula.WhitLow_k :=
  _root_.PositivityTheory.SiegelWeilFormula.KWhit.whitLow_of_X_k _root_.PositivityTheory.SiegelWeilFormula.KWhit.iwaRedC_k _root_.PositivityTheory.SiegelWeilFormula.KWhit.vacSpan_k _root_.PositivityTheory.SiegelWeilFormula.KWhit.linRedC_k _root_.PositivityTheory.SiegelWeilFormula.KWhit.coreX_k _root_.PositivityTheory.SiegelWeilFormula.KWhit.genDictX_of_k hVK hT hA hF hS hU hEW hW hTC hLB hPK
end PositivityTheory.SiegelWeilFormula.KWhit
end
end
