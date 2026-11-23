import Mathlib
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.PowTwoSymplecticRelation
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.GermComp1ZeroPointLeft
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.pow_two_symplectic_relation : ∀ (R : Type) [CommRing R] (d : ℕ) (O : Type) [CommRing O] [StarRing O] (B : FB R d O) (n : ℕ), pow2 B n * B.sy ^ n = ev (n := 2) ![pt R d 0, comp1 (B.A.act (n : O)) (pt R d 1)] B.sy * ev (n := 2) ![pt R d 1, pt R d 0] (pow1 B n) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Conj.pow_sy_exchange | exact GlobalTheory.CompanionTheory.Ar.Conj.pow_sy_exchange | (intros; apply GlobalTheory.CompanionTheory.Ar.Conj.pow_sy_exchange <;> assumption)
