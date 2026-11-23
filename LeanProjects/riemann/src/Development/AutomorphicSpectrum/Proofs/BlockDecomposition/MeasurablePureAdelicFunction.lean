import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ThPr
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PureAdelicFunctionFormula
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology Filter GroundTheory.Global PositivityTheory.Rg.Base1 GlobalTheory.CompanionTheory.BasePsi
open scoped ENNReal NNReal Classical

noncomputable section

namespace GlobalTheory.CompanionTheory.BasePsi

theorem measurable_pure_rv_zero (F : Type) [Field F] [NumberField F]
    (S : Finset (HeightOneSpectrum (𝓞 F))) (G : Ainf F → ℝ)
    (g : ∀ v : HeightOneSpectrum (𝓞 F), Fv F v → ℝ) (hG : Continuous G)
    (hg : ∀ v ∈ S, Continuous (g v)) :
    Measurable (PositivityTheory.Rg.Base1.pure S G g fun v => rv v 0) := by
  have : BorelSpace (AF F) := ⟨rfl⟩
  have hval : Measurable (Units.val : (AF F)ˣ → AF F) := comap_measurable _
  have hfst : Continuous (fun x : AF F => x.1) := continuous_fst
  have hev : ∀ v : HeightOneSpectrum (𝓞 F), Continuous (fun x : AF F => x.2 v) := fun v =>
    (RestrictedProduct.continuous_eval v).comp continuous_snd
  have hc : Continuous (fun x : AF F => G x.1 * ∏ v ∈ S, g v (x.2 v)) :=
    (hG.comp hfst).mul (continuous_finsetProd _ fun v hv => (hg v hv).comp (hev v))
  have hopen : IsOpen {x : AF F | ∀ v, v ∉ S → x.2 v ∈ v.adicCompletionIntegers F} :=
    (RestrictedProduct.isOpen_forall_imp_mem (fun v => Valued.isOpen_valuationSubring _)
      (p := fun v : HeightOneSpectrum (𝓞 F) => v ∉ S)).preimage continuous_snd
  have hh : Measurable (fun x : AF F => if ∀ v, v ∉ S → x.2 v ∈ v.adicCompletionIntegers F then
      ENNReal.ofReal (G x.1 * ∏ v ∈ S, g v (x.2 v)) else 0) :=
    Measurable.ite hopen.measurableSet (ENNReal.measurable_ofReal.comp hc.measurable)
      measurable_const
  have he : (PositivityTheory.Rg.Base1.pure S G g fun v => rv v 0) = (fun x : AF F =>
      if ∀ v, v ∉ S → x.2 v ∈ v.adicCompletionIntegers F then
        ENNReal.ofReal (G x.1 * ∏ v ∈ S, g v (x.2 v)) else 0) ∘ Units.val :=
    funext fun a => GlobalTheory.CompanionTheory.BasePsi.pure_rv_zero_apply S G g a
  rw [he]
  exact hh.comp hval

end GlobalTheory.CompanionTheory.BasePsi

end
