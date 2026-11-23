import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArithmeticMixedVolumeKillsDifference
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SemiposAtOfPositive
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.BasicNotions.TH Formalism.L2.Theta ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O
open scoped ENNReal Classical
open MvPolynomial Formalism.BasicNotions.DV
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.arithmetic_mixed_volume_kills_difference : Hypotheses2 → HypothesesH → ∀ (D : D7) (O : Setup D), O.Core → ∀ (Sx : Finset ℕ) (R : ℝ), 2 ≤ R → ∀ (p : ℕ), p.Prime → ∀ (τ : D.what₂.Tau) (k : ℕ), 1 ≤ k → ∀ (y : Rt D.what₂.Tau O.Y.N) (g : MvPolynomial (Vm D.what₂.Tau O.Y.N) ℝ), O.Y.arMix Sx R p (tagHT D.what₂.Tau _ (pk D _ τ k) * ((X (Sum.inl (false, y)) - X (Sum.inl (true, y))) * g)) = 0 := by
  first | exact @GlobalTheory.TrivFlag.arMix_powerSum_mul_vertical | exact GlobalTheory.TrivFlag.arMix_powerSum_mul_vertical | (intros; apply GlobalTheory.TrivFlag.arMix_powerSum_mul_vertical <;> assumption)
