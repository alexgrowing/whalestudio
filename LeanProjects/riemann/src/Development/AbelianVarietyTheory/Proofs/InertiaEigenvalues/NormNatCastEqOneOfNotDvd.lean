import Mathlib

universe u_1

namespace GlobalTheory.NatCastUnitNorm

theorem norm_natCast_eq_one_of_not_dvd {K : Type u_1} [inst : NormedField K] [IsUltrametricDist K]
    {l m : ℕ} (hl : Nat.Prime l) (hlt : ‖(l : K)‖ < (1 : ℝ)) (hm : ¬ l ∣ m) :
    ‖(m : K)‖ = (1 : ℝ) := by
  have hle : ‖(m : K)‖ ≤ 1 := IsUltrametricDist.norm_natCast_le_one K m
  by_contra hne
  have hmlt : ‖(m : K)‖ < 1 := lt_of_le_of_ne hle hne
  have hcop : Nat.Coprime l m := (Nat.Prime.coprime_iff_not_dvd hl).2 hm
  obtain ⟨a, b, hab⟩ : IsCoprime (l : ℤ) (m : ℤ) := Nat.isCoprime_iff_coprime.2 hcop
  have hK : (a : K) * (l : K) + (b : K) * (m : K) = 1 := by
    have h := congrArg (fun z : ℤ => (z : K)) hab
    simpa using h
  have key : ∀ (c : ℤ) (x : K), ‖x‖ < 1 → ‖(c : K) * x‖ < 1 := by
    intro c x hx
    rw [norm_mul]
    have hc : ‖(c : K)‖ ≤ 1 := IsUltrametricDist.norm_intCast_le_one K c
    calc ‖(c : K)‖ * ‖x‖ ≤ 1 * ‖x‖ := mul_le_mul_of_nonneg_right hc (norm_nonneg x)
      _ = ‖x‖ := one_mul _
      _ < 1 := hx
  have h1 := IsUltrametricDist.norm_add_le_max ((a : K) * (l : K)) ((b : K) * (m : K))
  rw [hK, norm_one] at h1
  exact absurd h1 (not_le.2 (max_lt (key a _ hlt) (key b _ hmlt)))

end GlobalTheory.NatCastUnitNorm
