import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TwistedCoefficientMeasurableBounded
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.KFiniteVectors.KFiniteThetaLifts.PureThetaTransfer.ConstantTermModerateGrowth
open NumberField IsDedekindDomain MeasureTheory GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic Ad3 Ad3.K Ad3.K.QuadraticBaseChangeGL3 Ad3.K.QuadraticBaseChangeGL3.Th
open GroundTheory.Automorphic.GodementSection (localChar)
open GroundTheory.Automorphic.Reduction (finAt infAt maxCompact)
open GroundTheory.Automorphic.GLnLocal (integralGL)
open Ad3.R (G2 Jd md KA LInv IsLoc2 pt pri dia2)
open scoped NumberField.AdeleRing ValuativeRel

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twisted_coefficient_measurable_bounded : ∀ (K : Type) [Field K] [NumberField K] (c : HeckeCharacter K) (M : ∀ v : Pl, LM c v) (Sv : Finset Pl) (m : Pl →₀ ℤ),
  Measurable (fun u => ctM M Sv m u) ∧ ∀ u, ‖ctM M Sv m u‖ ≤ 1 := by
  first | exact @GlobalTheory.CompanionTheory.CtMeas.measurable_ctM_norm_le | exact GlobalTheory.CompanionTheory.CtMeas.measurable_ctM_norm_le | (intros; apply GlobalTheory.CompanionTheory.CtMeas.measurable_ctM_norm_le <;> assumption)
