import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.StandardLocalCoefficientValues
import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsReps
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SplitPlaceEmbeddingPropertiesStatement
open NumberField IsDedekindDomain MeasureTheory GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic Ad3 Ad3.K Ad3.K.QuadraticBaseChangeGL3 Ad3.K.QuadraticBaseChangeGL3.Th
open GroundTheory.Automorphic.GodementSection (localChar)
open GroundTheory.Automorphic.Reduction (finAt infAt maxCompact)
open GroundTheory.Automorphic.GLnLocal (integralGL)
open Ad3.R (G2 Jd md KA LInv IsLoc2 pt pri dia2)
open scoped NumberField.AdeleRing ValuativeRel
open GroundTheory.Global.AdicLiesOver
open GlobalTheory.CompanionTheory.FexTheta

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.standard_local_coefficient_values : ∀ (K : Type) [Field K] [NumberField K], Module.finrank ℚ K = 2 → ∀ (c : HeckeCharacter K) (v : Pl) (L : LM c v),
  L.ok → Unr c v → L.std → ∀ k ∈ integralGL (Qv v) 2, ∀ κ : Kˣ,
  (∀ w : PlK K, w.asIdeal.LiesOver v.asIdeal → ((atW w κ : (Kv K w)ˣ) : Kv K w) ∈ 𝒪[Kv K w] ∧
    (((atW w κ)⁻¹ : (Kv K w)ˣ) : Kv K w) ∈ 𝒪[Kv K w]) →
  fL L k (κ : K) 1 = 1 ∧ (L.IsSp → ∀ j : ℤ, j ≠ 0 → fL L k (κ : K) (unifUnit (Qv v) ^ j) = 0) := by
  first | exact @GlobalTheory.CompanionTheory.FexTheta.StdLocal.fL_std | exact GlobalTheory.CompanionTheory.FexTheta.StdLocal.fL_std | (intros; apply GlobalTheory.CompanionTheory.FexTheta.StdLocal.fL_std <;> assumption)
