import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NonNormWeilConstantValue
import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.KFiniteVectors.LocalWhittakerDuality.WSteps
import GroundTheory.LocalFields.QuadraticAbelian.WeilRepQuadratic

open MeasureTheory Matrix GroundTheory.LocalField GroundTheory.Automorphic Ad3 Ad3.K.GL2LocalData
open GroundTheory.LocalField.FiltrationCocycleLiftCriterion.WeilRep
open scoped ValuativeRel
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.non_norm_weil_constant_value : (∀ (F E : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [MeasurableSpace F] [BorelSpace F] [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
  [MeasurableSpace E] [BorelSpace E] [Algebra F E] [ValuativeExtension F E] [FiniteDimensional F E]
  [Algebra.IsSeparable F E] [Fact (Module.finrank F E = 2)], Continuous (algebraMap F E) → ∀ a : Fˣ, a ∉ (normUnits F E).range → ∃ κ : ENNReal, κ ≠ ⊤ ∧ ∀ S : Set F, MeasurableSet S →
  haarIntegers E ((Algebra.norm F : E → F) ⁻¹' S) + (modulus (a : F) : ENNReal) * haarIntegers E ((fun u : E => (a : F) * Algebra.norm F u) ⁻¹' S) = κ * haarIntegers F S) → ForEF fun F _ _ _ _ _ _ _ E _ _ _ _ _ _ _ χ σ η => ∀ (a : Fˣ), (¬ ∃ t : Eˣ, Algebra.norm F (t : E) = a) → ∀ N₀ : ℤ,
  ∃ n₁ ≤ N₀, ∃ n₂ ≤ N₀,
    (∫ u in (valBall E n₁ : Set E), (χ (Algebra.norm F u) : ℂ) ∂muE E χ) +
      ((modulus (a : F) : ℝ) : ℂ) * ∫ u in (valBall E n₂ : Set E), (χ ((a : F) * Algebra.norm F u) : ℂ) ∂muE E χ = 0 := by
  first | exact @GlobalTheory.CompanionTheory.WeilGaussNon.ball_integrals_cancel | exact GlobalTheory.CompanionTheory.WeilGaussNon.ball_integrals_cancel | (intros; apply GlobalTheory.CompanionTheory.WeilGaussNon.ball_integrals_cancel <;> assumption)
