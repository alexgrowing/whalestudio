import Mathlib

namespace Bl.FirstBlockLemmaC

theorem goal1 :
  ∀ {p : Nat} [inst : Fact (Nat.Prime p)] {m : Nat},
  Ne.{1} m 0 → ∀ {ζ : PadicAlgCl p}, Eq.{1} (HPow.hPow.{0, 0, 0} ζ m) 1 → Eq.{1} (Norm.norm.{0} ζ) 1 := by
  intro p _ m hm ζ h
  have h1 : ‖ζ‖ ^ m = 1 := by rw [← norm_pow, h, norm_one]
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) hm).mp h1

end Bl.FirstBlockLemmaC
