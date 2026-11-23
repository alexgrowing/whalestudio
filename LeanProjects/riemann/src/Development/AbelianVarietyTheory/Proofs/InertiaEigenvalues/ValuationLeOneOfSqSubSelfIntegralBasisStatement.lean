import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ValuationLeOneOfSqSubSelfIntegralBasis
import Mathlib
open NumberField IsDedekindDomain TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.valuation_le_one_of_sq_sub_self_integral_basis : ∀ (E E' : Type) [Field E] [NumberField E] [Field E'] [NumberField E'] [Algebra E E'] {ι : Type} [Fintype ι] (b : Module.Basis ι E E'), (∀ i, IsIntegral ℤ (b i)) → ∀ (w : HeightOneSpectrum (𝓞 E)) (w'' : HeightOneSpectrum (𝓞 E')), w''.asIdeal.comap (algebraMap (𝓞 E) (𝓞 E')) = w.asIdeal → ∀ ε : E', (∀ i, w.valuation E (b.repr (ε * ε - ε) i) ≤ 1) → w''.valuation E' ε ≤ 1 := by
  first | exact @GlobalTheory.integral_of_sq_sub_integral | exact GlobalTheory.integral_of_sq_sub_integral | (intros; apply GlobalTheory.integral_of_sq_sub_integral <;> assumption)
