import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ThetaSeriesVanishesLargeModule
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ThPr
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PureAdelicFunctionFormulaStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.BoundedDenominatorsCompactIdeleSetStatement
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology Filter GroundTheory.Global PositivityTheory.Rg.Base1 GlobalTheory.CompanionTheory.BasePsi
open scoped ENNReal NNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.theta_series_vanishes_large_module : ∀ (F : Type) [Field F] [NumberField F] (S : Finset (HeightOneSpectrum (𝓞 F))) (G : Ainf F → ℝ)
    (g : ∀ v : HeightOneSpectrum (𝓞 F), Fv F v → ℝ), HasCompactSupport G → (∀ v ∈ S, HasCompactSupport (g v)) →
    ∃ R : ℝ, ∀ a : (AF F)ˣ, R < md a → th (PositivityTheory.Rg.Base1.pure S G g fun v => rv v 0) a = 0 := by
  first | exact @GlobalTheory.CompanionTheory.BasePsi.th_pure_vanish | exact GlobalTheory.CompanionTheory.BasePsi.th_pure_vanish | (intros; apply GlobalTheory.CompanionTheory.BasePsi.th_pure_vanish <;> assumption)
