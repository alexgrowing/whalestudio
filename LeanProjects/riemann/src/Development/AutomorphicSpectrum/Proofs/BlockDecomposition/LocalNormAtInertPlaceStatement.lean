import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LocalNormAtInertPlace
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
theorem _root_.GlobalTheory.T.local_norm_at_inert_place : ∀ (K : Type) [Field K] [NumberField K], Module.finrank ℚ K = 2 → ∀ (v : Pl) (w : PlK K) [w.asIdeal.LiesOver v.asIdeal],
  (∀ w' : PlK K, w'.asIdeal.LiesOver v.asIdeal → w' = w) → ∀ ξ : K,
    Algebra.norm (Qv v) (algebraMap K (Kv K w) ξ) = ((Algebra.norm ℚ ξ : ℚ) : Qv v) := by
  first | exact @GlobalTheory.CompanionTheory.FexTheta.local_norm_eq_of_unique_place | exact GlobalTheory.CompanionTheory.FexTheta.local_norm_eq_of_unique_place | (intros; apply GlobalTheory.CompanionTheory.FexTheta.local_norm_eq_of_unique_place <;> assumption)
