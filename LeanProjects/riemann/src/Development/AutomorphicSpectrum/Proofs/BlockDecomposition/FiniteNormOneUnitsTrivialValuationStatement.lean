import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteNormOneUnitsTrivialValuation
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
theorem _root_.GlobalTheory.T.finite_norm_one_units_trivial_valuation : ∀ (K : Type) [Field K] [NumberField K], Module.finrank ℚ K = 2 → IsTotallyComplex K →
  ∀ (c : HeckeCharacter K) (M : ∀ v : Pl, LM c v), AdmM M → Finite {κ : K1 K // vK M (κ : Kˣ) = 0} := by
  first | exact @GlobalTheory.CompanionTheory.FexTheta.finite_stabiliser | exact GlobalTheory.CompanionTheory.FexTheta.finite_stabiliser | (intros; apply GlobalTheory.CompanionTheory.FexTheta.finite_stabiliser <;> assumption)
