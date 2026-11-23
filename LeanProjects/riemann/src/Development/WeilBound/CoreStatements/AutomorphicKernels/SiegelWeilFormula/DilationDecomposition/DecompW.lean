import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.DilationDecomposition.Assembly
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.DilationDecomposition.SplitDomOf
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.DilationDecomposition.Bridge
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.DilationDecomposition.ContinuousMhUInv
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.ThetaSplitting.SplitW
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.SiegelSetUnitaryStatement

noncomputable section

open scoped TensorProduct NNReal Matrix SchwartzMap Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
open GlobalTheory.Doubling (absE)

namespace PositivityTheory.SiegelWeilFormula.Kdil

theorem decompW : DecompW := fun _ _ _ _ _ _ _ _ d R w g => KSplitW.decompW d R w g

theorem gIdil (hT : TAll) (hAux : AuxiliaryPrimeFunction) (hLE : LocOpEx) (hAw : AwayAct) (hS : GlobalTheory.Published.SiegelSetUnitary)
    (hLF : LocFamG) (hBD : BigDense) : GIdil :=
  gIdil_of hT hAux hLE (thetaPt_of hT) (fun _ _ P => KFock.isSw_fP P) matCount (splitDom_of hT hAw decompW)
    (thetaBdd_of hS) hLF hBD holMean derCont stripOK

theorem gIdil' (hT : TAll) (hAux : AuxiliaryPrimeFunction) (hLE : LocOpEx) (hAw : AwayAct) (hLF : LocFamG) : GIdil :=
  gIdil hT hAux hLE hAw GlobalTheory.T.siegel_set_unitary hLF bigDense

end PositivityTheory.SiegelWeilFormula.Kdil

end
