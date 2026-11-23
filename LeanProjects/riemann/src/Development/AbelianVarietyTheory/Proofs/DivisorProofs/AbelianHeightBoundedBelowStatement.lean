import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbelianHeightBoundedBelow
import Development.AbelianVarietyTheory.Definitions.Divisors.SemiposAtOfPositive
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O
open scoped ENNReal Classical

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.abelian_height_bounded_below : Hypotheses2 → HypothesesH → ∀ (D : D7) (O : Setup D), O.Core → ∀ c : O.s.Comp, ∃ C : ℝ, ∀ b : (O.var c).X, IsClosed ({b} : Set (O.var c).X) → -C ≤ (O.met.ab c).ht b := by
  first | exact @GlobalTheory.AmpleHtLow.main | exact GlobalTheory.AmpleHtLow.main | (intros; apply GlobalTheory.AmpleHtLow.main <;> assumption)
