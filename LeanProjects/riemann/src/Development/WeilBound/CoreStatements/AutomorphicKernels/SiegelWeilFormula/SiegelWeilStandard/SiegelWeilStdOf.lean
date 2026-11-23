import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.FockVacuumBounds.SiegelWeilStdLeaves
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.ThetaBijections.JjMulJj
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.ThetaParabolic.TThetaSum
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SchrodingerCommutation.TthetaComm
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.ThetaAutomorphy.ThetaAutoAt
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.ThetaAutomorphy.ContinuousTt
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.UnfoldingCompactness.UnfoldOf
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.ThetaSplitting.SplitCut
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.ThetaSplitting.GIinvCut
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.VacuumIwasawa.VacTop
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.VacuumIwasawa.IwaTop
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.AwayActions.AwayActOfTAll
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LocalWeilOperators.LocOpExOfTAll
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.UnramifiedWhittaker.UnrWhitOf
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.ZetaEulerProducts.ZetaInvPoOfOneLt
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.RealGaussianTraces.CpowProdOfReal
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.RealGaussianTraces.RealLowOf
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.WhittakerGlobalFactors.FactorCore
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.WhittakerLowRank.WhitGenLowOf
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.WhittakerCovolume.GenDictXOf
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LocalCharacterIntegrals.LocFin2
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.AdelicFormCongruences.JointT
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.AdelicDilations.NdZero
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.SiegelSetUnitaryStatement
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.MollifiedIntegrability.Imports
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.MinorFormulas.SPrime
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.HolomorphicTheta.HolomorphicAverageUniform
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.BaseOneSide.BaseOneOf
import Development.WeilBound.CoreStatements.AutomorphicKernels.UnitarySchrodingerModel.UnitarySchrodingerLemmas.LowRankSiegelDensities.ChapterTop

noncomputable section

open GlobalTheory.ThK.Dbl PositivityTheory.Rg.Sw

namespace PositivityTheory.SiegelWeilFormula.Fin

theorem tTheta : TTheta := Tpar.tTheta_of (tweyl.tthetaComm TBij.tBij)

theorem tAll_of (hW : TWeyl) : TAll := ⟨TBij.tBij, Tpar.tPar, hW, tTheta, Tauto.thetaAuto GlobalTheory.T.siegel_set_unitary Tpar.tPar tTheta⟩

theorem thetaCoef : ThetaCoef := Tauto.thetaCoef GlobalTheory.T.siegel_set_unitary TBij.tBij Tpar.tPar tTheta

theorem whitGenLt : Gen.WhitGenLt :=
  Gen.whitGenLtOf SwLocFin.locFin2 Gunr.unrWhit (GReal.realWhit_of WR.wr) GFac.factorX PositivityTheory.PfSWUS.HMass.siegelDensitiesLowA

theorem whitGenEq : Gen.WhitGenEq :=
  Gen.whitGenEqOf SwLocFin.locFinX Gunr.unrWhitX (GReal.realWhitEq_of WR.wr) GFac.factorX Gen.lOrd PositivityTheory.Rg.Base1.densEq

theorem whitGenLow : Gen.WhitGenLow :=
  Gen.whitGenLowOf SwLocFin.locFinX Gunr.unrWhitX (GReal.realLow_of SP.wrOrd) GFac.factorX Gen.lOrd

theorem siegelWeilStd_of (hT : TAll) (hLI : LocInst) (hGD : GIdil) (hKP : KFinPoly) (hPK : PolyKFin) (hLD : LDEx)
    (hCT : CTSplit) (hH : HolLead) : SiegelWeilStd := by
  have hA : AuxiliaryPrimeFunction := kfour.auxEx
  have hF : FockMem := KFock.fockMem
  have hLo : LocOpEx := locOpEx_of_tAll hT
  have hGS : GSplit := KSplit.gSplit_of hF (KAway.awayAct_of_tAll hT)
  have hVK : VacK := Avac.vacK_of hT hF hLo hLI (KAway.finAct_of_tAll hT)
  have hW : WhitK := KWhit.whitK_of hT hA Krd.rdEx hF hKP Khead.secK kunf.unfold whitGenLt thetaCoef kfour.lamBd hPK
  have hWE : WhitEq :=
    KWhit.whitEq_of hT hA Krd.rdEx hF hKP Khead.secK kunf.unfold Aeis.eisWk whitGenEq thetaCoef kfour.lamBd hPK
  have hWL : WhitLow := KWhit.whitLow_of hVK hT hA hF Khead.secK kunf.unfold Aeis.eisWk whitGenLow thetaCoef kfour.lamBd hPK
  have hSt : Step := AStep.stepOf hH Holtb.holT hT thetaCoef hA kfour.coefEx hF (KFock.liftEx hT.1) hLo hLI hGS hPK Khead.secK
    Aeis.eisWk kfour.lamBd (KSing.lamSing_of kfour.coefEx kfour.fourierZero Krd.denseW hA) kfour.fourierZero kunf.unfold hWL hVK
    (Avac.iwaQ_of' hT) hCT Afc.uEx (Afc.fcConj_of hA) Afc.orbRes
  exact Atop.siegelWeilStd_of AbsSt.absThm hT thetaCoef hLo hLI hGS (KSplit.gIinv_of hT hF) hGD hKP hPK kunf.unfold hW hWE
    AbsSt.vacuum_generates_polynomials hLD hVK hSt

end PositivityTheory.SiegelWeilFormula.Fin

end
