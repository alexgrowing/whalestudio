import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DenseClosedPointsBoundedHeight
import Development.AbelianVarietyTheory.Definitions.Divisors.SemiposAtOfPositive
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O
open scoped ENNReal Classical

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dense_closed_points_bounded_height : Hypotheses2 → HypothesesH → ∀ (D : D7) (O : Setup D), O.Core → ∀ c : O.s.Comp, ∃ S : Set (O.var c).X, (∀ b ∈ S, IsClosed ({b} : Set (O.var c).X)) ∧ Dense S ∧ ∃ C : ℝ, ∀ b ∈ S, (O.met.ab c).ht b ≤ C := by
  first | exact @GlobalTheory.CovHt.denseBoundedHtAb | exact GlobalTheory.CovHt.denseBoundedHtAb | (intros; apply GlobalTheory.CovHt.denseBoundedHtAb <;> assumption)
