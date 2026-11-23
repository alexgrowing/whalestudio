import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Fun0FitOfJoin
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Realised
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LeafInfinitePlaceBound
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.FittedFunctionAtZeroClose

set_option synthInstance.maxHeartbeats 200000

section
section
namespace GlobalTheory.BigTop.Fun.Close
theorem fourier_coefficient_fit_of_join_alt : _root_.GlobalTheory.FunPr.ThetaLocalInputs → GlobalTheory.Mem.LiteralAutomorphy.JoinOut → GlobalTheory.Published.HeckeTateFunctionalEquation → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching → GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup.FunctionalsSeparate → _root_.GlobalTheory.BigTop.LambdaLowerBound₂ → _root_.GlobalTheory.BigTop.Fun.ConstantFunctionFits @GlobalTheory.BigTop.Fun.Fld := by
  intro hP hJ hHT hTheta hLoc hSep hLam
  obtain ⟨hTD, hTr, hTw, hZD, hRefl⟩ :=
    hJ
  exact _root_.GlobalTheory.BigTop.Fun.Close.fittedFunction_at_zero_close_alt hP (GlobalTheory.Published.HeckeTateFunctionalEquation.abs hHT) hTD hTr hTw hZD hRefl
    hTheta hLoc hSep hLam
end GlobalTheory.BigTop.Fun.Close
end
end
