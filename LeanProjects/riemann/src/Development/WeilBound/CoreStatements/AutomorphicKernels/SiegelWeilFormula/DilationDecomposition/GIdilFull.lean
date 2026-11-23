import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.DilationDecomposition.DecompW
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.DilationDecomposition.LocDone

noncomputable section

open scoped TensorProduct NNReal Matrix SchwartzMap Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
open GlobalTheory.Doubling (absE)

namespace PositivityTheory.SiegelWeilFormula.Kdil

theorem gIdil_full (hT : TAll) (hAux : AuxiliaryPrimeFunction) (hLE : LocOpEx) (hAw : AwayAct) (hLI : LocInst) : GIdil :=
  gIdil' hT hAux hLE hAw (locFamG_done hT hAux (fun _ _ P => KFock.isSw_fP P) hLI)

end PositivityTheory.SiegelWeilFormula.Kdil

end
