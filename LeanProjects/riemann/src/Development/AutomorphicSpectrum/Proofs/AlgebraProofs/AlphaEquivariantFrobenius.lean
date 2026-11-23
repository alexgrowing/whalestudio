import Mathlib
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.GermComp1ZeroPointLeft
import Development.WeilBound.CoreStatements.HodgeTatePoints.CbAlpha

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Conj.AlphaAct

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj

theorem alpha_comm_act : ∀ (R : Type) [CommRing R] (p : ℕ) [Fact p.Prime] [CharP R p] (d : ℕ) (O : Type) [CommRing O] [StarRing O] (B : FB R d O) (a : O) (u : Fin d → R), alpha B p (((rho B a).map (· ^ p)).mulVec u) = rhoH B a (alpha B p u) :=
  @PositivityTheory.HtPt.Cb.alpha_act

end GlobalTheory.CompanionTheory.Ar.Conj.AlphaAct
