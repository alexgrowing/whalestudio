import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PureAdelicFunctionFormula
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ThPr
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology Filter GroundTheory.Global PositivityTheory.Rg.Base1 GlobalTheory.CompanionTheory.BasePsi
open scoped ENNReal NNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pure_adelic_function_formula : ∀ (F : Type) [Field F] [NumberField F] (S : Finset (HeightOneSpectrum (𝓞 F))) (G : Ainf F → ℝ)
    (g : ∀ v : HeightOneSpectrum (𝓞 F), Fv F v → ℝ) (a : (AF F)ˣ),
    PositivityTheory.Rg.Base1.pure S G g (fun v => rv v 0) a =
      if ∀ v, v ∉ S → (a : AF F).2 v ∈ v.adicCompletionIntegers F then
        ENNReal.ofReal (G (a : AF F).1 * ∏ v ∈ S, g v ((a : AF F).2 v)) else 0 := by
  first | exact @GlobalTheory.CompanionTheory.BasePsi.pure_rv_zero_apply | exact GlobalTheory.CompanionTheory.BasePsi.pure_rv_zero_apply | (intros; apply GlobalTheory.CompanionTheory.BasePsi.pure_rv_zero_apply <;> assumption)
