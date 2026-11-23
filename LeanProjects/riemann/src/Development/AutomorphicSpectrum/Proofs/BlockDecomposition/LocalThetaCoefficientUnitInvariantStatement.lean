import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalThetaCoefficientUnitInvariant
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
theorem _root_.GlobalTheory.T.local_theta_coefficient_unit_invariant : ∀ (K : Type) [Field K] [NumberField K], Module.finrank ℚ K = 2 → ∀ (c : HeckeCharacter K) (v : Pl) (L : LM c v),
  L.ok → (¬ L.IsSp ∨ (Unr c v ∧ L.std)) → ∀ (g : GL (Fin 2) (Qv v)) (ξ : K) (x : (Qv v)ˣ),
    ∀ e ∈ unQ v, fL L g ξ (x * e) = fL L g ξ x := by
  first | exact @GlobalTheory.CompanionTheory.FexTheta.fL_mul_unit | exact GlobalTheory.CompanionTheory.FexTheta.fL_mul_unit | (intros; apply GlobalTheory.CompanionTheory.FexTheta.fL_mul_unit <;> assumption)
