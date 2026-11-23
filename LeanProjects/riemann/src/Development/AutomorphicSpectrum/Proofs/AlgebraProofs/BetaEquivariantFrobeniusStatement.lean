import Mathlib
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.BetaEquivariantFrobenius
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.GermComp1ZeroPointLeft
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.beta_equivariant_frobenius : ∀ (R : Type) [CommRing R] (p : ℕ) [Fact p.Prime] [CharP R p] (d : ℕ) (O : Type) [CommRing O] [StarRing O] (B : FB R d O) (a : O) (y : (Fin d → R) × (Fin d → R)), beta B p (rhoH B a y) = ((rho B (star a)).transpose.map (· ^ p)).mulVec (beta B p y) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Conj.beta_rhoH_eq | exact GlobalTheory.CompanionTheory.Ar.Conj.beta_rhoH_eq | (intros; apply GlobalTheory.CompanionTheory.Ar.Conj.beta_rhoH_eq <;> assumption)
