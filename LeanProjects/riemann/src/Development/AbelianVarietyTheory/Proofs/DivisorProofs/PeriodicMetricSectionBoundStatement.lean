import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PeriodicMetricSectionBound
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DbarEqZeroOfHolomorphic
open Matrix GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe GlobalTheory.TorsionForm GlobalTheory.TorsionForm.FlatAcyc
open scoped Real ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.periodic_metric_section_bound : ∀ {g : ℕ} (T : Matrix (Fin g) (Fin g) ℂ) (hT : GlobalTheory.IsSiegel T)
    (M : Submodule ℤ (Fl g)) (hM : IsLat M) (H : (Fin g → ℂ) → ℝ) (hH : ContDiff ℝ ∞ H)
    (hHpos : ∀ z, 0 < H z) (u : (Fin g → ℂ) → ℂ) (hu : ContDiff ℝ ∞ u)
    (J : Fl g → (Fin g → ℂ) → ℂ) (hu_per : ∀ l ∈ M, ∀ z, u (z + per T l) = J l z * u z)
    (hdu_per : ∀ l ∈ M, ∀ z c, d01 u (z + per T l) (ev c) = J l z * d01 u z (ev c))
    (hH_per : ∀ l ∈ M, ∀ z, H (z + per T l) * ‖J l z‖ ^ 2 = H z) (k : ℝ) (hk : 0 < k)
    (heq : ∀ z, ∑ a, ∑ c, ((2 : ℂ) • T.map fun t => (t.im : ℂ)) a c *
      (d10 (fun z' => d01 u z' (ev c)) z (ev a) +
        d10 (fun z' => (Real.log (H z') : ℂ)) z (ev a) * d01 u z (ev c)) = k * u z),
    ∀ z, u z = 0 := by
  first | exact @GlobalTheory.ScalarAcyc.vanish | exact GlobalTheory.ScalarAcyc.vanish | (intros; apply GlobalTheory.ScalarAcyc.vanish <;> assumption)
