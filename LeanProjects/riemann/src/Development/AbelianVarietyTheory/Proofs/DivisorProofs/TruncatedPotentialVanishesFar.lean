import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SemiposAtOfPositive
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf

set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O
open scoped ENNReal Classical

namespace GlobalTheory.ChgZeroFar

theorem phR_eq_zero : Hypotheses2 → HypothesesH → OnObj fun _ O _ T _ _ => ∀ c u σ (R : ℝ), 2 ≤ R → ∀ x, x ∉ (T.M c).Z σ → R ^ 3 ≤ (T.M c).r σ x → (T.F c).phR R u σ x = 0 := by
  intro _ _ D O hO _ A T H h c u σ R hR x hxZ hr
  refine ((h.an c).phR R hR u σ x).trans (hO.chg_some_eq_zero c _ hR u (Or.inr ?_))
  exact hr.trans_eq ((h.an c).r σ x hxZ)

end GlobalTheory.ChgZeroFar

end
