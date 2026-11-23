import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.DataExOf
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.DiagCommOf
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.SetupAlgPf
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.UniformizerValuations.PeakTraceBoundHolds

namespace PositivityTheory.Rg.BcB.F

theorem runFin_chain (hF : F5.FinFam) (hW : WeightEx) (hQ : PermSat) (hD : Eig.DiagAlg) (hG : GenEx) : One.RunFin :=
  F5.runFin_of (runT_of peak_trace_bound_holds (setupEx_of setupAlg (dataEx_of (diagComm_of hD) genToData hG))) hF hW hQ

end PositivityTheory.Rg.BcB.F
