import Mathlib
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.WeierstrassPSuperlatticeHalfPeriodProd
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.LatIntZero
open GlobalTheory.MomOne GlobalTheory.MomN PowerSeries
open scoped ComplexConjugate
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weierstrassP_superlattice_half_period_prod : ∀ (L L' : PeriodPair) (T : Finset ℂ) (w : ℂ), L.lattice ≤ L'.lattice → (∀ t ∈ T, t ∈ L'.lattice ∧ t ∉ L.lattice) → (∀ t ∈ T, ∀ t' ∈ T, t - t' ∈ L.lattice → t = t') → (∀ x ∈ L'.lattice, x ∈ L.lattice ∨ ∃ t ∈ T, x - t ∈ L.lattice) → 2 * w ∈ L.lattice → w ∉ L'.lattice → ∀ z, z ∉ L'.lattice → (L'.weierstrassP z - L'.weierstrassP w) * ∏ t ∈ T, (L.weierstrassP z - L.weierstrassP t) = (L.weierstrassP z - L.weierstrassP w) * ∏ t ∈ T, (L.weierstrassP z - L.weierstrassP (w + t)) := by
  first | exact @GlobalTheory.HalfPeriodProduct.wp_half_period_prod | exact GlobalTheory.HalfPeriodProduct.wp_half_period_prod | (intros; apply GlobalTheory.HalfPeriodProduct.wp_half_period_prod <;> assumption)
