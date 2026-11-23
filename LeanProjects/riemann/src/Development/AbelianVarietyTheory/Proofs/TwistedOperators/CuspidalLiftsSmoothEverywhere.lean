import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RangeSndRel
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CuspAlongSmoothRows
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NegativeThetaLevelFirstStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NegativeThetaLevelSecondStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NegativeThetaLevelThirdStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NegativeThetaLevelFourthStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HorizontalThetaLevelFirstStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HorizontalThetaLevelSecondStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HorizontalThetaLevelThirdStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HorizontalThetaLevelFourthStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NegativeParabolicThetaFirstStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NegativeParabolicThetaSecondStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NegativeParabolicThetaThirdStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NegativeParabolicThetaFourthStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NegativeParabolicThetaFifthStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NegativeParabolicThetaSixthStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NegativeParabolicThetaSeventhStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NegativeParabolicThetaEighthStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.VerticalThetaLevelFirstStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.VerticalThetaLevelSecondStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.VerticalThetaLevelThirdStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.VerticalThetaLevelFourthStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.CuspSmoothLift

theorem liftsCuspidalSmoothAt_of_liftsCuspidal : GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.LiftsCuspidal → GlobalTheory.FunPr.Hypotheses₂ → ∀ D : D7, GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.LiftsCuspidalSmoothAt D := by
  intro hL hP D hS G₀ _ _ Pl0 T A Ks _ _ _ R G hR hG
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro t i j hi hj Φ hΦ φ hφ
    have hc := GlobalTheory.T.negative_theta_level_first hL hP D hS G₀ Pl0 T A Ks R G hR hG t i j hi hj Φ hΦ φ hφ
    exact ⟨hc, GlobalTheory.T.negative_theta_level_second hL hP D hS G₀ Pl0 T A Ks R G hR hG t i j hi hj Φ hΦ φ hφ hc, GlobalTheory.T.negative_theta_level_third hL hP D hS G₀ Pl0 T A Ks R G hR hG t i j hi hj Φ hΦ φ hφ hc, GlobalTheory.T.negative_theta_level_fourth hL hP D hS G₀ Pl0 T A Ks R G hR hG t i j hi hj Φ hΦ φ hφ hc⟩
  · intro t i j hi hj Φ hΦ φ hφ
    have hc := GlobalTheory.T.horizontal_theta_level_first hL hP D hS G₀ Pl0 T A Ks R G hR hG t i j hi hj Φ hΦ φ hφ
    exact ⟨hc, GlobalTheory.T.horizontal_theta_level_second hL hP D hS G₀ Pl0 T A Ks R G hR hG t i j hi hj Φ hΦ φ hφ hc, GlobalTheory.T.isCuspFun_theta_integral_of_integrableOn hL hP D hS G₀ Pl0 T A Ks R G hR hG t i j hi hj Φ hΦ φ hφ hc, GlobalTheory.T.horizontal_theta_level_fourth hL hP D hS G₀ Pl0 T A Ks R G hR hG t i j hi hj Φ hΦ φ hφ hc⟩
  · intro i hi Φ hΦ φ hφ
    have hc := GlobalTheory.T.negative_parabolic_theta_first hL hP D hS G₀ Pl0 T A Ks R G hR hG i hi Φ hΦ φ hφ
    exact ⟨hc, GlobalTheory.T.isAutFunSm_thetaLift_of_isCuspOfType hL hP D hS G₀ Pl0 T A Ks R G hR hG i hi Φ hΦ φ hφ hc, GlobalTheory.T.negative_parabolic_theta_third hL hP D hS G₀ Pl0 T A Ks R G hR hG i hi Φ hΦ φ hφ hc, GlobalTheory.T.negative_parabolic_theta_fourth hL hP D hS G₀ Pl0 T A Ks R G hR hG i hi Φ hΦ φ hφ hc⟩
  · intro i hi Φ hΦ φ hφ
    have hc := GlobalTheory.T.negative_parabolic_theta_fifth hL hP D hS G₀ Pl0 T A Ks R G hR hG i hi Φ hΦ φ hφ
    exact ⟨hc, GlobalTheory.T.negative_parabolic_theta_sixth hL hP D hS G₀ Pl0 T A Ks R G hR hG i hi Φ hΦ φ hφ hc, GlobalTheory.T.negative_parabolic_theta_seventh hL hP D hS G₀ Pl0 T A Ks R G hR hG i hi Φ hΦ φ hφ hc, GlobalTheory.T.negative_parabolic_theta_eighth hL hP D hS G₀ Pl0 T A Ks R G hR hG i hi Φ hΦ φ hφ hc⟩
  · intro t j hj Φ hΦ φ hφ
    have hc := GlobalTheory.T.vertical_theta_level_first hL hP D hS G₀ Pl0 T A Ks R G hR hG t j hj Φ hΦ φ hφ
    exact ⟨hc, GlobalTheory.T.vertical_theta_level_second hL hP D hS G₀ Pl0 T A Ks R G hR hG t j hj Φ hΦ φ hφ hc, GlobalTheory.T.vertical_theta_level_third hL hP D hS G₀ Pl0 T A Ks R G hR hG t j hj Φ hΦ φ hφ hc, GlobalTheory.T.vertical_theta_level_fourth hL hP D hS G₀ Pl0 T A Ks R G hR hG t j hj Φ hΦ φ hφ hc⟩

end GlobalTheory.CuspSmoothLift

end
