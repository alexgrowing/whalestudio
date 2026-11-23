import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.MemRangeWittAlgClosureOfBoundedRingHom
import Mathlib
import Formalism.LocalToGlobal.GroupLattices.PendingLemmas.InvarianceIffAdditiveMapsExist
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_range_witt_algClosure_of_bounded_ringHom : ∀ (p : ℕ) [Fact p.Prime] (n : ℕ) (W : Type) [CommRing W], 0 < n → (∀ x : W, (p : W) ∣ x ^ (p ^ n) - x) → IsAdicComplete (Ideal.span {(p : W)}) W → ∀ φ : W →+* ℂ_[p], (∀ x, ‖φ x‖ ≤ 1) → ∀ x, φ x ∈ Set.range (Formalism.L2.G.Pend.wToC p) := by
  first | exact @GlobalTheory.mem_range_wToC_of_pow_congr | exact GlobalTheory.mem_range_wToC_of_pow_congr | (intros; apply GlobalTheory.mem_range_wToC_of_pow_congr <;> assumption)
