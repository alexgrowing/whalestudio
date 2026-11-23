import Mathlib
import Development.AutomorphicSpectrum.Proofs.MetricProofs.SncResolutionRegularLocalRing
import Development.AutomorphicSpectrum.Proofs.MetricProofs.FiniteMinimalPrimes
open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo GlobalTheory.CompanionTheory.Ar.Cmp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.snc_resolution_regular_local_ring : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Ω : Type) [Field Ω] [CharZero Ω] (y : (Σ k, ι k) → Ω) (e : ℕ) (J : Ideal (MRing ι)), IsArithVar (mCoordIdeal y) (e + 1) → IsSncModel y e J → ∀ p : (k : K) → ι k, ∀ x ∈ SncRes.src (pC (mCoordIdeal y)) p, IsRegularLocalRing (ReciprocityTheory.AnForm.R.locRing (SncRes.ideal (pC (mCoordIdeal y)) p) (SncRes.coord (pC (mCoordIdeal y)) p x)) ∧ ringKrullDim (ReciprocityTheory.AnForm.R.locRing (SncRes.ideal (pC (mCoordIdeal y)) p) (SncRes.coord (pC (mCoordIdeal y)) p x)) = e := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.Reg.isRegularLocalRing_chart | exact GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.Reg.isRegularLocalRing_chart | (intros; apply GlobalTheory.CompanionTheory.Ar.Cmp.SncRes.Reg.isRegularLocalRing_chart <;> assumption)
