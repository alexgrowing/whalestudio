import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UnitMeasureFiniteCompactSupport
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.KFiniteVectors.KFiniteThetaLifts.PureThetaTransfer.ConstantTermModerateGrowth
open NumberField IsDedekindDomain MeasureTheory GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic Ad3 Ad3.K Ad3.K.QuadraticBaseChangeGL3 Ad3.K.QuadraticBaseChangeGL3.Th
open GroundTheory.Automorphic.GodementSection (localChar)
open GroundTheory.Automorphic.Reduction (finAt infAt maxCompact)
open GroundTheory.Automorphic.GLnLocal (integralGL)
open Ad3.R (G2 Jd md KA LInv IsLoc2 pt pri dia2)
open scoped NumberField.AdeleRing ValuativeRel

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.unit_measure_finite_compact_support : ∀ Sv : Finset Pl, IsFiniteMeasure (muU Sv) ∧ (∀ᵐ u ∂(muU Sv), ∀ v : Sv, u v ∈ unQ v.1) ∧ ∀ v : Pl, IsCompact (unQ v) := by
  first | exact @GlobalTheory.CompanionTheory.ThetaUnits.muU_finite_units | exact GlobalTheory.CompanionTheory.ThetaUnits.muU_finite_units | (intros; apply GlobalTheory.CompanionTheory.ThetaUnits.muU_finite_units <;> assumption)
