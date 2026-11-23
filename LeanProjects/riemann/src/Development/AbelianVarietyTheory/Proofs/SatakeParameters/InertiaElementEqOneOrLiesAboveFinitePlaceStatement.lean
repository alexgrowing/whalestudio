import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.InertiaElementEqOneOrLiesAboveFinitePlace
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModGDefs
open NumberField IsDedekindDomain Neutral.HilbertClassField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.inertiaElement_eq_one_or_liesAbove_finitePlace : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (g : Ω ≃ₐ[E] Ω), ReciprocityTheory.ChartRestriction.L1.InertiaEl A g → g = 1 ∨ ∃ v : HeightOneSpectrum (𝓞 E), LiesAbove A v := by
  first | exact @GlobalTheory.inertiaEl_eq_one_or_liesAbove | exact GlobalTheory.inertiaEl_eq_one_or_liesAbove | (intros; apply GlobalTheory.inertiaEl_eq_one_or_liesAbove <;> assumption)
