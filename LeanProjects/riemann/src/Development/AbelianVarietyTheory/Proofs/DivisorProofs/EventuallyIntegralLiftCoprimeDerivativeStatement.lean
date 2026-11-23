import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyIntegralLiftCoprimeDerivative
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnifAt
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eventually_integral_lift_coprime_derivative : ∀ (E : Type) [Field E] [NumberField E] (P : E[X]), P.Separable →
    ∀ᶠ w : HeightOneSpectrum (𝓞 E) in cofinite, ∃ P₀ : (w.adicCompletionIntegers E)[X],
      P₀.map (algebraMap (w.adicCompletionIntegers E) (w.adicCompletion E)) = P.map (algebraMap E (w.adicCompletion E)) ∧
      IsCoprime P₀ (derivative P₀) := by
  first | exact @GlobalTheory.IntCop.eventually_integral_coprime | exact GlobalTheory.IntCop.eventually_integral_coprime | (intros; apply GlobalTheory.IntCop.eventually_integral_coprime <;> assumption)
