import Mathlib
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.PowOneSeriesPFormula
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.GermComp1ZeroPointLeft
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pow_one_series_p_formula : ∀ (R : Type) [CommRing R] (p : ℕ) [Fact p.Prime] [CharP R p] (d : ℕ) (O : Type) [CommRing O] [StarRing O] (B : FB R d O), ∃ g : PS R 2 d, AxOne g ∧ pow1 B p = ev (n := 2) ![ptPow R d p 0, pt R d 1] g ∧ bil g 1 1 = am B p := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Conj.pow_one_series_in_p | exact GlobalTheory.CompanionTheory.Ar.Conj.pow_one_series_in_p | (intros; apply GlobalTheory.CompanionTheory.Ar.Conj.pow_one_series_in_p <;> assumption)
