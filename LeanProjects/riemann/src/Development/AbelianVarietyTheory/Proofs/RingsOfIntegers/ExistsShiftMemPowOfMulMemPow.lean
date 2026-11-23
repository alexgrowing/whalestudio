import Mathlib

namespace GlobalTheory.ShiftMemPowOfMulMemPow

theorem exists_shift_mem_pow_of_mul_mem_pow {R : Type} [CommRing R] [IsDomain R]
    [IsNoetherianRing R] (I : Ideal R) {r : R} (hr : r ≠ 0) :
    ∃ c : ℕ, ∀ (n : ℕ) (x : R), r * x ∈ I ^ (n + c) → x ∈ I ^ n := by
  obtain ⟨k, hk⟩ := Ideal.exists_pow_inf_eq_pow_smul I (Ideal.span {r} : Submodule R R)
  refine ⟨k, fun n x hx => ?_⟩
  have h1 : r * x ∈ I ^ (n + k) • (⊤ : Submodule R R) ⊓ Ideal.span {r} := by
    refine Submodule.mem_inf.mpr ⟨?_, Ideal.mem_span_singleton'.mpr ⟨x, mul_comm _ _⟩⟩
    rw [Ideal.smul_eq_mul, Ideal.mul_top]
    exact hx
  rw [hk (n + k) (Nat.le_add_left k n), Nat.add_sub_cancel] at h1
  have h2 : r * x ∈ I ^ n * Ideal.span {r} := Submodule.smul_mono le_rfl inf_le_right h1
  obtain ⟨z, hz, hzr⟩ := Ideal.mem_mul_span_singleton.mp h2
  have hzx : z = x := mul_right_cancel₀ hr (by rw [hzr, mul_comm])
  exact hzx ▸ hz

end GlobalTheory.ShiftMemPowOfMulMemPow
