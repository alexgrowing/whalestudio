import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ThetaSeriesUniformBoundCompact
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ThPr
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PureAdelicFunctionFormulaStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.BoundedDenominatorsCompactIdeleSetStatement
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology Filter GroundTheory.Global PositivityTheory.Rg.Base1 GlobalTheory.CompanionTheory.BasePsi
open scoped ENNReal NNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.theta_series_uniform_bound_compact : ∀ (F : Type) [Field F] [NumberField F], IsTotallyReal F → ∀ θ : ℝ →+* Ainf F, Continuous θ → ∀ r : ℝ → (AF F)ˣ, IsRay θ r →
    ∀ (S : Finset (HeightOneSpectrum (𝓞 F))) (G : Ainf F → ℝ) (g : ∀ v : HeightOneSpectrum (𝓞 F), Fv F v → ℝ),
    Continuous G → HasCompactSupport G → (∀ v ∈ S, Continuous (g v) ∧ HasCompactSupport (g v)) →
    ∀ D : Set (AF F)ˣ, IsCompact D → ∃ C : ℝ≥0, ∀ u ∈ D, ∀ δ : ℝ, 0 < δ →
      ENNReal.ofReal (δ ^ Module.finrank ℚ F) * th (PositivityTheory.Rg.Base1.pure S G g fun v => rv v 0) (u * r δ) ≤ C := by
  first | exact @GlobalTheory.CompanionTheory.BasePsi.th_pure_rv_zero_bound | exact GlobalTheory.CompanionTheory.BasePsi.th_pure_rv_zero_bound | (intros; apply GlobalTheory.CompanionTheory.BasePsi.th_pure_rv_zero_bound <;> assumption)
