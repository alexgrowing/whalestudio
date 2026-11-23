import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MeasurablePureAdelicFunction
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ThPr
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PureAdelicFunctionFormulaStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.BoundedDenominatorsCompactIdeleSetStatement
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology Filter GroundTheory.Global PositivityTheory.Rg.Base1 GlobalTheory.CompanionTheory.BasePsi
open scoped ENNReal NNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.measurable_pure_adelic_function : ∀ (F : Type) [Field F] [NumberField F] (S : Finset (HeightOneSpectrum (𝓞 F))) (G : Ainf F → ℝ)
    (g : ∀ v : HeightOneSpectrum (𝓞 F), Fv F v → ℝ), Continuous G → (∀ v ∈ S, Continuous (g v)) →
    Measurable (PositivityTheory.Rg.Base1.pure S G g fun v => rv v 0) := by
  first | exact @GlobalTheory.CompanionTheory.BasePsi.measurable_pure_rv_zero | exact GlobalTheory.CompanionTheory.BasePsi.measurable_pure_rv_zero | (intros; apply GlobalTheory.CompanionTheory.BasePsi.measurable_pure_rv_zero <;> assumption)
