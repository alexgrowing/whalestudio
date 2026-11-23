import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.FockVacuumBounds.SiegelWeilStdLeaves
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.SplitStab
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.IsLatRepL
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilDatumProperties
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.LiftedSchrodingerDatum
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.BaseKnownTheoremsS
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.BaseKnownTheoremsE
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelMultOfK
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKheadSecK
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKfourW
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKrdRD
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKfockFock
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKfourLB
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKsingTop
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKfourNA
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKfourFZ
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKrdDenseW
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilAeisWk
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKmainMain
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SWStdLtK
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKheadHead
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKheadStrong
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilAtopMainEq
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilAtopVacAll
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilAtopMainLe
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilAtopFieldOf

set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix SchwartzMap Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
namespace PositivityTheory.SiegelWeilFormula
theorem Atop.siegelWeilStd_of_k (hA : AbsThm) (hT : _root_.PositivityTheory.SiegelWeilFormula.TAll_k) (hTC : _root_.PositivityTheory.SiegelWeilFormula.ThetaCoef_k) (hLo : _root_.PositivityTheory.SiegelWeilFormula.LocOpEx_k) (hLI : _root_.PositivityTheory.SiegelWeilFormula.LocInst_k)
    (hGS : _root_.PositivityTheory.SiegelWeilFormula.GSplit_k) (hGI : _root_.PositivityTheory.SiegelWeilFormula.GIinv_k) (hGD : _root_.PositivityTheory.SiegelWeilFormula.GIdil_k) (hKP : _root_.PositivityTheory.SiegelWeilFormula.KFinPoly_k) (hPK : _root_.PositivityTheory.SiegelWeilFormula.PolyKFin_k) (hU : _root_.PositivityTheory.SiegelWeilFormula.Unfold_k)
    (hW : _root_.PositivityTheory.SiegelWeilFormula.WhitK_k) (hWE : _root_.PositivityTheory.SiegelWeilFormula.WhitEq_k) (hG : AbsSt.GenCore) (hLD : _root_.PositivityTheory.SiegelWeilFormula.LDEx_k) (hVK : _root_.PositivityTheory.SiegelWeilFormula.VacK_k) (hSt : _root_.PositivityTheory.SiegelWeilFormula.Step_k) :
    _root_.GlobalTheory.ThK.Dbl.SiegelWeilStd_k := by
  have hBL : _root_.GlobalTheory.ThK.Dbl.EisBL_k := _root_.PositivityTheory.RgEis.Hd.eisBL_k
  have hSK : _root_.PositivityTheory.SiegelWeilFormula.SecK_k := _root_.PositivityTheory.SiegelWeilFormula.Khead.secK_k
  have hAux : _root_.PositivityTheory.SiegelWeilFormula.SiegelWeilDatumProperties := _root_.PositivityTheory.SiegelWeilFormula.kfour.auxiliaryExistence_holds
  have hRD : _root_.PositivityTheory.SiegelWeilFormula.RDEx_k := _root_.PositivityTheory.SiegelWeilFormula.Krd.rdEx_k
  have hFM : _root_.PositivityTheory.SiegelWeilFormula.FockMem_k := _root_.PositivityTheory.SiegelWeilFormula.KFock.fockMem_k
  have hLE : _root_.PositivityTheory.SiegelWeilFormula.LiftEx_k := _root_.PositivityTheory.SiegelWeilFormula.KFock.liftEx_k hT.1
  have hLB : _root_.PositivityTheory.SiegelWeilFormula.LamBd_k := _root_.PositivityTheory.SiegelWeilFormula.kfour.lamBd_k
  have hLS : _root_.PositivityTheory.SiegelWeilFormula.LamSing_k := _root_.PositivityTheory.SiegelWeilFormula.KSing.lamSing_of_k _root_.PositivityTheory.SiegelWeilFormula.kfour.coefEx_k _root_.PositivityTheory.SiegelWeilFormula.kfour.fourierZero_k _root_.PositivityTheory.SiegelWeilFormula.Krd.denseW_k hAux
  have hEW : _root_.PositivityTheory.SiegelWeilFormula.EisWk_k := _root_.PositivityTheory.SiegelWeilFormula.Aeis.eisWk_k
  have hMain := _root_.PositivityTheory.SiegelWeilFormula.KMain.mainOf_k hA hT hTC hRD hAux hFM hLE hLo hLI hGS hGI hGD hKP hPK hSK hLB hLS hU hW
  have hLt := _root_.PositivityTheory.SiegelWeilFormula.Khead.headOf_k hBL hSK (_root_.PositivityTheory.SiegelWeilFormula.Khead.eisStrong_of_k hBL) hMain
  have hEq := _root_.PositivityTheory.SiegelWeilFormula.Atop.mainEq_of_k hA hT hTC hRD hAux hFM hLE hLo hLI hGS hGI hGD hKP hPK hSK hLB hLS hU hEW hWE
  have hVA := _root_.PositivityTheory.SiegelWeilFormula.Atop.vacAllOfC_k hG hT hAux hFM hLE hLo hLI hGS hGI hGD hKP hPK hSK hEW
  have hLe := _root_.PositivityTheory.SiegelWeilFormula.Atop.mainLeOf_k hRD hLD hVK hPK hEq hSt hVA
  exact _root_.PositivityTheory.SiegelWeilFormula.Atop.fieldOf_k hBL hSK hLt hLe
end PositivityTheory.SiegelWeilFormula
end
end
