import Mathlib

namespace GlobalTheory.ThetaWeight

open Finset

variable {ι : Type*} [Fintype ι]

def size (m : ℤ) (G : (ι → ℤ) × ℤ) : ℤ := ∑ i, |G.1 i| + m * G.2 + 1

theorem one_le_size {m : ℤ} (hm : 0 ≤ m) {G : (ι → ℤ) × ℤ} (hG : 0 ≤ G.2) : 1 ≤ size m G := by
  have h1 : 0 ≤ ∑ i, |G.1 i| := sum_nonneg fun i _ => abs_nonneg _
  have h2 := mul_nonneg hm hG
  unfold size
  linarith

end GlobalTheory.ThetaWeight
