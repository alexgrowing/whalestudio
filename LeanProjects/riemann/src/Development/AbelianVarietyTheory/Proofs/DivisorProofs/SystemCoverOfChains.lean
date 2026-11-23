import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLocallyNoetherianBase
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonemptyRChainOfIsUnit
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OmegaMapPolBCBijective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BarSmulDualVec
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DvdIffOfCompletion
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OmegaMapHodgeTate
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLinearExtendPi
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDualFamily
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCombInt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGlobalRoots
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftBaseChangeDualBijective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MapOmegaMapTanForm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullbackCompHomApp
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValFCrdResM
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpMapEpsMulOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDualBasis

set_option autoImplicit false

namespace GlobalTheory.ChainPts.SysB

theorem sysCoverSt : GlobalTheory.CovTop.Hypotheses2 → GlobalTheory.CovHt.HypothesesH → GlobalTheory.Published.PrismaticDieudonnePerfd →
    GlobalTheory.GroupBplus.GroupAllSt → GlobalTheory.RingChain.ExistsSt → GlobalTheory.RingChain.MapSt → GlobalTheory.ChainPts.SysCoverSt :=
  fun _ _ hD hG hE hM => sysCoverSt_of_steps (GlobalTheory.ChainPts.SysB.RingEx.ringExSt_of_existsSt hE) (GlobalTheory.ChainPts.SysB.RingRes.ringRes hM)
    (GlobalTheory.ChainPts.SysB.RingAct.ringAct hM) GlobalTheory.ChainPts.SysB.RingJ.ringJSt GlobalTheory.ChainPts.SysB.KerRho.ker_rho
    GlobalTheory.ChainPts.SysB.kerRSt GlobalTheory.ChainPts.SysB.OmegaRes.omegaResSt GlobalTheory.ChainPts.SysB.HT.htSt
    GlobalTheory.ChainPts.SysB.exists_global_roots GlobalTheory.ChainPts.SecPair.pairSt GlobalTheory.ChainPts.DualAct.actSt
    GlobalTheory.ChainPts.SysB.Form.formSt GlobalTheory.ChainPts.SysB.FormRes.formResSt GlobalTheory.ChainPts.SysB.FormAct.formActSt
    GlobalTheory.ChainPts.SysB.TanDual.tanSt hD hG

end GlobalTheory.ChainPts.SysB
