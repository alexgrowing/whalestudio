import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothGreenPotentialWeight
import Development.AbelianVarietyTheory.Definitions.Divisors.SemiposAtOfPositive
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O
open scoped ENNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.smooth_green_potential_weight : Hypotheses2 → HypothesesH → OnObj fun _ O _ T _ _ => ∀ c, ∀ R : ℝ, Real.exp 2 ≤ R → ∀ w : Wt O.Y,
    (T.M c).Smooth ((T.F c).phR R w) := by
  first | exact @GlobalTheory.InterpChgSmooth.smooth_phR_of_exp_two_le | exact GlobalTheory.InterpChgSmooth.smooth_phR_of_exp_two_le | (intros; apply GlobalTheory.InterpChgSmooth.smooth_phR_of_exp_two_le <;> assumption)
