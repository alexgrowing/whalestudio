import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsPadicIntOfCompatibleZmodPow
import Mathlib
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_padicInt_of_compatible_zmod_pow' : ∀ (p : ℕ) [Fact p.Prime] (c : ∀ n : ℕ, ZMod (p ^ n)), (∀ n₁ n₂ (h : n₁ ≤ n₂), ZMod.castHom (pow_dvd_pow p h) (ZMod (p ^ n₁)) (c n₂) = c n₁) → ∃ z : ℤ_[p], ∀ n, PadicInt.toZModPow n z = c n := by
  first | exact @GlobalTheory.exists_padicInt_of_compatible_zmod_pow | exact GlobalTheory.exists_padicInt_of_compatible_zmod_pow | (intros; apply GlobalTheory.exists_padicInt_of_compatible_zmod_pow <;> assumption)
