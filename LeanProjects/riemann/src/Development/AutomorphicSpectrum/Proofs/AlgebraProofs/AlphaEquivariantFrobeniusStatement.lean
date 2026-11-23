import Mathlib
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.AlphaEquivariantFrobenius
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.GermComp1ZeroPointLeft
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.alpha_equivariant_frobenius : ∀ (R : Type) [CommRing R] (p : ℕ) [Fact p.Prime] [CharP R p] (d : ℕ) (O : Type) [CommRing O] [StarRing O] (B : FB R d O) (a : O) (u : Fin d → R), alpha B p (((rho B a).map (· ^ p)).mulVec u) = rhoH B a (alpha B p u) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Conj.AlphaAct.alpha_comm_act | exact GlobalTheory.CompanionTheory.Ar.Conj.AlphaAct.alpha_comm_act | (intros; apply GlobalTheory.CompanionTheory.Ar.Conj.AlphaAct.alpha_comm_act <;> assumption)
