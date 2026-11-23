import Mathlib
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.PowerSeriesPowPFrobenius
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.GermComp1ZeroPointLeft
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.power_series_pow_p_frobenius : ∀ (R : Type) [CommRing R] (p : ℕ) [Fact p.Prime] [CharP R p] (d n : ℕ) (f : PS R n d), f ^ p = ev (fun j => ptPow R d p j) (MvPowerSeries.map (frobenius R p) f) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Conj.pow_eq_ev_frobenius | exact GlobalTheory.CompanionTheory.Ar.Conj.pow_eq_ev_frobenius | (intros; apply GlobalTheory.CompanionTheory.Ar.Conj.pow_eq_ev_frobenius <;> assumption)
