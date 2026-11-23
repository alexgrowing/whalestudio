import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SplitPlaceEmbeddingProperties
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
theorem _root_.GlobalTheory.T.split_place_embedding_properties : ∀ (K : Type) [Field K] [NumberField K], Module.finrank ℚ K = 2 → ∀ (v : Pl) (w₁ w₂ : PlK K)
  [w₁.asIdeal.LiesOver v.asIdeal] [w₂.asIdeal.LiesOver v.asIdeal], w₁ ≠ w₂ →
    (∀ ξ : K, algebraMap (Qv v) (Kv K w₁) (dg1 v w₁ ξ) = algebraMap K (Kv K w₁) ξ) ∧
    (∀ ξ : K, algebraMap (Qv v) (Kv K w₂) (dg1 v w₂ ξ) = algebraMap K (Kv K w₂) ξ) ∧
    ∀ ξ : K, dg1 v w₁ ξ * dg1 v w₂ ξ = ((Algebra.norm ℚ ξ : ℚ) : Qv v) := by
  first | exact @GlobalTheory.CompanionTheory.SpAlg.split_place_embeddings_norm | exact GlobalTheory.CompanionTheory.SpAlg.split_place_embeddings_norm | (intros; apply GlobalTheory.CompanionTheory.SpAlg.split_place_embeddings_norm <;> assumption)
