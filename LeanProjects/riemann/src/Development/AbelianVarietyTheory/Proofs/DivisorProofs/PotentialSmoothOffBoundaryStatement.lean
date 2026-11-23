import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PotentialSmoothOffBoundary
import Development.AbelianVarietyTheory.Definitions.Divisors.SemiposAtOfPositive
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O
open scoped ENNReal Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.potential_smooth_off_boundary : Hypotheses2 → HypothesesH → OnObj fun _ O _ T _ _ => ∀ c u σ, ((T.M c).A σ).SmoothOn ((T.M c).Z σ)ᶜ ((T.F c).ph u σ) := by
  first | exact @GlobalTheory.HodgeChgSmooth.smoothOn_ph | exact GlobalTheory.HodgeChgSmooth.smoothOn_ph | (intros; apply GlobalTheory.HodgeChgSmooth.smoothOn_ph <;> assumption)
