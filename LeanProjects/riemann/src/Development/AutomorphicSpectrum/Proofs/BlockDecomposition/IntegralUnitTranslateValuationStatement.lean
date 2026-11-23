import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IntegralUnitTranslateValuation
import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsReps
open NumberField IsDedekindDomain MeasureTheory GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic Ad3 Ad3.K Ad3.K.QuadraticBaseChangeGL3 Ad3.K.QuadraticBaseChangeGL3.Th
open GroundTheory.Automorphic.GodementSection (localChar)
open GroundTheory.Automorphic.Reduction (finAt infAt maxCompact)
open GroundTheory.Automorphic.GLnLocal (integralGL)
open Ad3.R (G2 Jd md KA LInv IsLoc2 pt pri dia2)
open scoped NumberField.AdeleRing ValuativeRel
open GroundTheory.Global.AdicLiesOver
open GlobalTheory.CompanionTheory.FexTheta

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.integral_unit_translate_valuation : ∀ (Sv : Finset Pl) (f : ∀ v : Pl, (Qv v)ˣ → ℂ), (∀ v ∉ Sv, ∀ x, ∀ e ∈ unQ v, f v (x * e) = f v x) →
  ∀ (k : ∀ v : Pl, (Qv v)ˣ) (m' : Pl →₀ ℤ), (∀ v, ord ((k v : (Qv v)ˣ) : Qv v) = m' v) → ∀ m : Pl →₀ ℤ,
    ∫ u, ∏ᶠ v, f v (tu Sv m u v * k v) ∂muU Sv = ∫ u, ∏ᶠ v, f v (tu Sv (m + m') u v) ∂muU Sv := by
  first | exact @GlobalTheory.CompanionTheory.FexTheta.torusAverage_shift | exact GlobalTheory.CompanionTheory.FexTheta.torusAverage_shift | (intros; apply GlobalTheory.CompanionTheory.FexTheta.torusAverage_shift <;> assumption)
