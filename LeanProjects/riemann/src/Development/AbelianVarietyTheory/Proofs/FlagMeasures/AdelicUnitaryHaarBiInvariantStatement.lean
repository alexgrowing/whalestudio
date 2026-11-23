import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AdelicUnitaryHaarBiInvariant
import Formalism.SharpRestriction.CuspSpanNormBounds.GlobAut
import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
open MeasureTheory Formalism.MainNotions.S NumberField
open scoped InnerProductSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adelicUnitaryHaar_bi_invariant : ∀ (I : AutInst) (μf : Measure I.Gf) [μf.IsHaarMeasure] [SigmaFinite μf], (∀ g : I.GA, Measure.map (fun x => g * x) (I.muA μf) = I.muA μf) ∧ (∀ g : I.GA, Measure.map (fun x => x * g) (I.muA μf) = I.muA μf) ∧ Measure.map (fun x : I.GA => x⁻¹) (I.muA μf) = I.muA μf ∧ (∀ g : I.Gf, Measure.map (fun x => x * g) μf = μf) ∧ ∀ U : Set I.GA, IsOpen U → U.Nonempty → 0 < I.muA μf U := by
  first | exact @GlobalTheory.AdelicUnimod.adelic_unimodular | exact GlobalTheory.AdelicUnimod.adelic_unimodular | (intros; apply GlobalTheory.AdelicUnimod.adelic_unimodular <;> assumption)
