import Mathlib
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.FormalGroupActionRingHom
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.GermComp1ZeroPointLeft
open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.formal_group_action_ring_hom : ∀ (R : Type) [CommRing R] (d : ℕ) (O : Type) [CommRing O] [StarRing O] (B : FB R d O), ∃ ρ : O →+* Matrix (Fin d) (Fin d) R, ∀ a, ρ a = rho B a := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Conj.rho_hom | exact GlobalTheory.CompanionTheory.Ar.Conj.rho_hom | (intros; apply GlobalTheory.CompanionTheory.Ar.Conj.rho_hom <;> assumption)
