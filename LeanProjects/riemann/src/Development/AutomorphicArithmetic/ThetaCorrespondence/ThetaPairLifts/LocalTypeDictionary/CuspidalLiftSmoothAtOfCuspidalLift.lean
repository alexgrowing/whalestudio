import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.DiscreteSpectrumResidualClassification
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CuspidalLiftsSmoothEverywhere
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.BernsteinUnitaryProductIrreducible
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.TwistedThetaKernelMulCuspFormIntegrableOn
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.TwistedThetaLiftIsSmoothAutomorphic
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.TwistedThetaLiftIsCuspidal
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.TwistedThetaLiftHasKType
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.ThetaIntegralIntegrableOnAutomorphicQuotient
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.TwistedThetaLiftOfCuspFormIsSmoothAutomorphic
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.TwistedThetaLiftOfCuspFormIsCuspidal
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.TwistedThetaLiftOfCuspFormHasKType
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.TwistedUpwardThetaIntegralConverges
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.TwistedUpwardThetaLiftIsSmoothAutomorphic
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.TwistedUpwardThetaLiftIsCuspidal
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.TwistedUpwardThetaLiftHasKType
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.TwistedDownwardThetaIntegralIntegrableOn
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.TwistedDownwardThetaLiftIsSmoothAutomorphic
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.DownwardThetaLiftIsCuspidalOfIntegrable
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.TwistedDownwardThetaLiftHasKType
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.ColumnConvolutionIntegrableOnSlice
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.ColumnLiftIsSmoothAutomorphicFunction
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.ColumnLiftIsCuspidalOfDefinite
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.LocalTypeDictionary.ColumnLiftHasTypeAtPlaces
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CuspidalLiftsSmoothEverywhereStatement

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
noncomputable section
namespace GlobalTheory.CuspSmoothLift
theorem cuspidal_lift_smooth_at_of_cuspidal_lift : GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.LiftsCuspidal → _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ D : D7, GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.LiftsCuspidalSmoothAt D := by
  intro hL hP D hS G₀ _ _ Pl0 T A Ks _ _ _ R G hR hG
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro t i j hi hj Φ hΦ φ hφ
    have hc := _root_.GlobalTheory.T.twisted_theta_kernel_mul_cusp_form_integrableOn hL hP D hS G₀ Pl0 T A Ks R G hR hG t i j hi hj Φ hΦ φ hφ
    exact ⟨hc, _root_.GlobalTheory.T.twisted_theta_lift_isSmoothAutomorphic hL hP D hS G₀ Pl0 T A Ks R G hR hG t i j hi hj Φ hΦ φ hφ hc, _root_.GlobalTheory.T.twisted_theta_lift_isCuspidal hL hP D hS G₀ Pl0 T A Ks R G hR hG t i j hi hj Φ hΦ φ hφ hc, _root_.GlobalTheory.T.twisted_theta_lift_hasKType hL hP D hS G₀ Pl0 T A Ks R G hR hG t i j hi hj Φ hΦ φ hφ hc⟩
  · intro t i j hi hj Φ hΦ φ hφ
    have hc := _root_.GlobalTheory.T.twisted_theta_integral_integrableOn_automorphic_quotient hL hP D hS G₀ Pl0 T A Ks R G hR hG t i j hi hj Φ hΦ φ hφ
    exact ⟨hc, _root_.GlobalTheory.T.twisted_theta_lift_of_cusp_form_isSmoothAutomorphic hL hP D hS G₀ Pl0 T A Ks R G hR hG t i j hi hj Φ hΦ φ hφ hc, _root_.GlobalTheory.T.twisted_theta_lift_of_cusp_form_isCuspidal hL hP D hS G₀ Pl0 T A Ks R G hR hG t i j hi hj Φ hΦ φ hφ hc, _root_.GlobalTheory.T.twisted_theta_lift_of_cusp_form_hasKType hL hP D hS G₀ Pl0 T A Ks R G hR hG t i j hi hj Φ hΦ φ hφ hc⟩
  · intro i hi Φ hΦ φ hφ
    have hc := _root_.GlobalTheory.T.twisted_upward_theta_integral_converges hL hP D hS G₀ Pl0 T A Ks R G hR hG i hi Φ hΦ φ hφ
    exact ⟨hc, _root_.GlobalTheory.T.twisted_upward_theta_lift_isSmoothAutomorphic hL hP D hS G₀ Pl0 T A Ks R G hR hG i hi Φ hΦ φ hφ hc, _root_.GlobalTheory.T.twisted_upward_theta_lift_isCuspidal hL hP D hS G₀ Pl0 T A Ks R G hR hG i hi Φ hΦ φ hφ hc, _root_.GlobalTheory.T.twisted_upward_theta_lift_hasKType hL hP D hS G₀ Pl0 T A Ks R G hR hG i hi Φ hΦ φ hφ hc⟩
  · intro i hi Φ hΦ φ hφ
    have hc := _root_.GlobalTheory.T.twisted_downward_theta_integral_integrableOn hL hP D hS G₀ Pl0 T A Ks R G hR hG i hi Φ hΦ φ hφ
    exact ⟨hc, _root_.GlobalTheory.T.twisted_downward_theta_lift_isSmoothAutomorphic hL hP D hS G₀ Pl0 T A Ks R G hR hG i hi Φ hΦ φ hφ hc, _root_.GlobalTheory.T.twisted_downward_theta_lift_isCuspidal hL hP D hS G₀ Pl0 T A Ks R G hR hG i hi Φ hΦ φ hφ hc, _root_.GlobalTheory.T.twisted_downward_theta_lift_hasKType hL hP D hS G₀ Pl0 T A Ks R G hR hG i hi Φ hΦ φ hφ hc⟩
  · intro t j hj Φ hΦ φ hφ
    have hc := _root_.GlobalTheory.T.columnConvolution_integrableOn hL hP D hS G₀ Pl0 T A Ks R G hR hG t j hj Φ hΦ φ hφ
    exact ⟨hc, _root_.GlobalTheory.T.columnLift_isAutomorphicFunction hL hP D hS G₀ Pl0 T A Ks R G hR hG t j hj Φ hΦ φ hφ hc, _root_.GlobalTheory.T.columnLift_isCuspForm hL hP D hS G₀ Pl0 T A Ks R G hR hG t j hj Φ hΦ φ hφ hc, _root_.GlobalTheory.T.columnLift_hasTypeAtPlaces hL hP D hS G₀ Pl0 T A Ks R G hR hG t j hj Φ hΦ φ hφ hc⟩
end GlobalTheory.CuspSmoothLift
end
end

section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cuspidal_lift_smooth_at_cusps : GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.LiftsCuspidal → _root_.GlobalTheory.FunPr.ThetaLocalInputs → ∀ D : D7, GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.LiftsCuspidalSmoothAt D := by
  first | exact @_root_.GlobalTheory.CuspSmoothLift.cuspidal_lift_smooth_at_of_cuspidal_lift | exact _root_.GlobalTheory.CuspSmoothLift.cuspidal_lift_smooth_at_of_cuspidal_lift | (intros; apply _root_.GlobalTheory.CuspSmoothLift.cuspidal_lift_smooth_at_of_cuspidal_lift <;> assumption)
end
