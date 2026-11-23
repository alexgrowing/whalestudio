import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SemiposAtOfPositive
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TruncatedPotentialSmooth
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O
open scoped ENNReal Classical

set_option autoImplicit false

theorem GlobalTheory.InterpChgSmooth.smooth_phR_of_exp_two_le : Hypotheses2 → HypothesesH → OnObj fun _ O _ T _ _ =>
    ∀ c, ∀ R : ℝ, Real.exp 2 ≤ R → ∀ w : Wt O.Y, (T.M c).Smooth ((T.F c).phR R w) := by
  intro h₁ h₂ D O hO hf A T H h c R hR w a
  have h2 : (2 : ℝ) ≤ R := by
    have := Real.add_one_le_exp (2 : ℝ)
    linarith
  exact GlobalTheory.InterpChgSmooth.smooth_phR h₁ h₂ D O hO hf A T H h c w a R h2
