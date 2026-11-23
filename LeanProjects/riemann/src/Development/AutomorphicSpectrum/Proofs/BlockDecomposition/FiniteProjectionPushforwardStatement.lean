import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteProjectionPushforward
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.AnalyticGerm
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StFiniteGermProjectionOpenAt
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StIrreducibleGermPrimitiveForm
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StPrimitiveFormSheetedOffDiscriminant
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StUnbranchedProperCountConstant
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StCentredDiscCoverCurve
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets Topology Filter
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_projection_pushforward : FiniteGermProjectionOpenAt.Statement → IrreducibleGermPrimitiveForm.Statement → PrimitiveFormSheetedOffDiscriminant.Statement → UnbranchedProperCountConstant.Statement → ∀ (σ : Type) [Fintype σ] (Y : Set (σ → ℂ)) (w : σ → ℂ) (A : (σ → ℂ) →L[ℂ] (Fin 1 → ℂ)), IsAnalyticNear Y w → GermIrreducibleAt Y w → (∃ W' ∈ 𝓝 w, ∀ x ∈ Y ∩ W', A x = A w → x = w) → (∀ h : (Fin 1 → ℂ) → ℂ, AnalyticAt ℂ h (A w) → (∀ᶠ z in 𝓝 w, z ∈ Y → h (A z) = 0) → ∀ᶠ y in 𝓝 (A w), h y = 0) → ∃ (Y' : Set (σ → ℂ)) (p : (σ → ℂ) →L[ℂ] ℂ) (ρ : ℝ) (N : ℕ), Y' ⊆ Y ∧ IsCentredDiscCover Y' w p ρ N := by
  first | exact @GlobalTheory.CompanionTheory.ComplexSets.irreducibleGerm_contains_centredDiscCover | exact GlobalTheory.CompanionTheory.ComplexSets.irreducibleGerm_contains_centredDiscCover | (intros; apply GlobalTheory.CompanionTheory.ComplexSets.irreducibleGerm_contains_centredDiscCover <;> assumption)
