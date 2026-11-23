import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalCoverBound
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Realised
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ChiMulPsiInvMemCoreStatement

set_option synthInstance.maxHeartbeats 200000

section
open NumberField
namespace GlobalTheory.CovTop
open GlobalTheory.BigTop Formalism.IndefR.FWT
variable {D : Formalism.BasicNotions.D7} {L : Formalism.BasicNotions.SizeData₂ D} {hT : Formalism.BasicNotions.GatTies D} {Gi : Formalism.MainNotions.G.Inst D L}
  {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts} {Y0 : Formalism.BasicNotions.DivX D} {cX : Formalism.BasicNotions.ExtraC}
  {ex : Formalism.BasicNotions.Extra D L hT Gi Gl Kc Y0 cX} {Csz : ℝ}
theorem ratAt_of_rows_alt (p : PtAt ex Csz) (i : Fin D.R.m) (hp : p.PointConditions') (ht : RecTied D L) : RatAt p i :=
  GlobalTheory.T.integralForms_eq_span_integralRationalForms _ _ _ _ _ _ _ _ (p.fw.ks i) (fun u f hf => rho_mem_WK p i u f hf) (_root_.GlobalTheory.T.chi_mul_psi_inv_mem_range_algebraMap p i hp ht)
end GlobalTheory.CovTop
end
