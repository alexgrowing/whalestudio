import Mathlib

namespace GlobalTheory.NatSmulMemIntegral

open NumberField

theorem exists_nat_mul_integral {E : Type} [Field E] [NumberField E] (a : E) :
    ∃ k : ℕ, k ≠ 0 ∧ ∃ b : RingOfIntegers E, (b : E) = (k : E) * a := by

  obtain ⟨y, hy0, hy⟩ := exists_integral_multiples ℤ ℚ (L := E) {a}
  have hi : IsIntegral ℤ (y • a) := hy a (Finset.mem_singleton_self a)
  refine ⟨y.natAbs, Int.natAbs_ne_zero.2 hy0, ?_⟩
  rcases Int.natAbs_eq y with hpos | hneg
  · refine ⟨⟨y • a, hi⟩, ?_⟩
    change y • a = _
    rw [zsmul_eq_mul]
    congr 1
    rw [Nat.cast_natAbs, abs_of_nonneg (by omega)]
  · refine ⟨-⟨y • a, hi⟩, ?_⟩
    change -(y • a) = _
    rw [zsmul_eq_mul, ← neg_mul]
    congr 1
    rw [Nat.cast_natAbs, abs_of_nonpos (by omega), Int.cast_neg]

theorem exists_nat_smul_mem {E : Type} [inst : Field E] [NumberField E] {n : ℕ}
    (Λ : Submodule (NumberField.RingOfIntegers E) (Fin n → E))
    (h : Submodule.span E (↑Λ : Set (Fin n → E)) = ⊤) (y : Fin n → E) :
    ∃ (m : ℕ), m ≠ (0 : ℕ) ∧ (↑m : E) • y ∈ Λ := by
  have hy : y ∈ Submodule.span E (↑Λ : Set (Fin n → E)) := by rw [h]; exact Submodule.mem_top
  simp only [Nat.cast_smul_eq_nsmul]
  induction hy using Submodule.span_induction with
  | mem x hx => exact ⟨1, one_ne_zero, by simpa using hx⟩
  | zero => exact ⟨1, one_ne_zero, by simp⟩
  | add x z _ _ hx hz =>
    obtain ⟨m₁, hm₁, h₁⟩ := hx
    obtain ⟨m₂, hm₂, h₂⟩ := hz
    refine ⟨m₂ * m₁, mul_ne_zero hm₂ hm₁, ?_⟩
    have ex : (m₂ * m₁) • x = m₂ • (m₁ • x) := by rw [mul_smul]
    have ez : (m₂ * m₁) • z = m₁ • (m₂ • z) := by rw [mul_comm, mul_smul]
    rw [smul_add, ex, ez]
    exact Λ.add_mem (Λ.nsmul_mem h₁ m₂) (Λ.nsmul_mem h₂ m₁)
  | smul c x _ hx =>
    obtain ⟨m, hm, hmx⟩ := hx
    obtain ⟨k, hk, b, hb⟩ := exists_nat_mul_integral c
    refine ⟨k * m, mul_ne_zero hk hm, ?_⟩
    have hbx : b • (m • x) ∈ Λ := Λ.smul_mem b hmx
    convert hbx using 1
    ext i
    simp only [Pi.smul_apply, smul_eq_mul, nsmul_eq_mul]
    rw [Algebra.smul_def, show (algebraMap (RingOfIntegers E) E b) = (b : E) from rfl, hb]
    simp only [Pi.mul_apply, Pi.natCast_apply, Nat.cast_mul]
    ring

end GlobalTheory.NatSmulMemIntegral
