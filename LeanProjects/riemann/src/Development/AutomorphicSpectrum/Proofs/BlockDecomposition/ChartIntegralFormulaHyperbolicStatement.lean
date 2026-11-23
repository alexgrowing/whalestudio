import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ChartIntegralFormulaHyperbolic
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FreeCell
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free GlobalTheory.CompanionTheory.WeilSiegel.HypStep GlobalTheory.CompanionTheory.WeilSiegel.HypStage
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chart_integral_formula_hyperbolic : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [MeasurableSpace R] [BorelSpace R], IsLocR R → ∀ (n d : ℕ) (b : Module.Basis (Fin d) F E) (lam : Measure R), lam.IsAddHaarMeasure → ∀ g : (Fin (n + 1) → Fin (M + 2) → R ⊗[F] E) → ℝ≥0∞, Measurable g → (∀ X, ¬ IsUnit (X 0 0) → g X = 0) → ∫⁻ X, g X ∂(coordW R b lam (n + 1) (M + 2)) = ∫⁻ x, ∫⁻ a, ∫⁻ s, ∫⁻ Y, g (chartS R σ J x a s Y) ∂(coordW R b lam n M) ∂(coordW R b lam 1 n) ∂(coordW R b lam 1 n) ∂(coordW R b lam 1 (M + 2)) := by
  first | exact @GlobalTheory.CompanionTheory.WeilSiegel.HypStage.chartS_lintegral | exact GlobalTheory.CompanionTheory.WeilSiegel.HypStage.chartS_lintegral | (intros; apply GlobalTheory.CompanionTheory.WeilSiegel.HypStage.chartS_lintegral <;> assumption)
