import Mathlib
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.GermComp1ZeroPointLeft
import Development.WeilBound.CoreStatements.HodgeTatePoints.CoeffEvPowOne

namespace GlobalTheory.CompanionTheory.Ar.Conj

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj

theorem pow_eq_ev_frobenius : ∀ (R : Type) [CommRing R] (p : ℕ) [Fact p.Prime] [CharP R p] (d n : ℕ) (f : PS R n d),
    f ^ p = ev (fun j => ptPow R d p j) (MvPowerSeries.map (frobenius R p) f) :=
  PositivityTheory.HtPt.Cb.frob_subst

end GlobalTheory.CompanionTheory.Ar.Conj
