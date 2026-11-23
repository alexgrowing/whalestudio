import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniquePowerSeriesOfCompatibleSystem
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.WittOnFalse
import Development.AbelianVarietyTheory.Definitions.Divisors.FormalCoboundarySmul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobKerIdealLeAugIdeal
open CategoryTheory TensorProduct MvPowerSeries GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Katz
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.existsUnique_powerSeries_of_compatible_system : ∀ (k : Type) [CommRing k] (σ : Type) [Finite σ] (B : ℕ → Type) [∀ n, CommRing (B n)] [∀ n, Algebra k (B n)] (y : ∀ n, σ → B n) (hy : ∀ n i, IsNilpotent (y n i)) (r : ∀ n, B (n + 1) →ₐ[k] B n), (∀ n i, r n (y (n + 1) i) = y n i) → Presents k y hy → ∀ b : ∀ n, B n, (∀ n, r n (b (n + 1)) = b n) → ∃! f : MvPowerSeries σ k, ∀ n, evA k (y n) (hy n) f = b n := by
  first | exact @GlobalTheory.Katz.existsUnique_evA_eq_of_presents | exact GlobalTheory.Katz.existsUnique_evA_eq_of_presents | (intros; apply GlobalTheory.Katz.existsUnique_evA_eq_of_presents <;> assumption)
