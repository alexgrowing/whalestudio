import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithmeticMixedVolumeParameterMaxTwo
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SemiposAtOfPositive
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O
open scoped ENNReal Classical
open MvPolynomial Formalism.BasicNotions.DV
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.arithmetic_mixed_volume_parameter_max_two : ∀ (D : D7) (O : Setup D), O.Core → ∀ (Sx : Finset ℕ) (R : ℝ) (p : ℕ), O.Y.arMix Sx R p = O.Y.arMix Sx (max R 2) p := by
  first | exact @GlobalTheory.ShFam.ParamTwo.arMix_eq_max_two | exact GlobalTheory.ShFam.ParamTwo.arMix_eq_max_two | (intros; apply GlobalTheory.ShFam.ParamTwo.arMix_eq_max_two <;> assumption)
