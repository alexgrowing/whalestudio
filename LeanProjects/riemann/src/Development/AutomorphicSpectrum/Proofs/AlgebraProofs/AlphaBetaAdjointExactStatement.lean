import Mathlib
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.AlphaBetaAdjointExact
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.GermComp1ZeroPointLeft
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.alpha_beta_adjoint_exact : ∀ (R : Type) [CommRing R] (p : ℕ) [Fact p.Prime] [CharP R p] (d : ℕ) (O : Type) [CommRing O] [StarRing O] (B : FB R d O), (∀ u y, u ⬝ᵥ beta B p y = pairH B (alpha B p u) y) ∧ beta B p ∘ₗ alpha B p = 0 := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Conj.Isotropy.beta_comp_alpha | exact GlobalTheory.CompanionTheory.Ar.Conj.Isotropy.beta_comp_alpha | (intros; apply GlobalTheory.CompanionTheory.Ar.Conj.Isotropy.beta_comp_alpha <;> assumption)
