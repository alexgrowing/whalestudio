import Mathlib

namespace GlobalTheory.NatMulIntegralExists

open NumberField

theorem exists_nat_mul_integral {E : Type} [Field E] [NumberField E] (a : E) :
    ∃ d : ℕ, 0 < d ∧ IsIntegral ℤ ((d : E) * a) := by
  have hz : IsAlgebraic ℤ a := IsFractionRing.isAlgebraic_iff ℤ ℚ E |>.mpr (.of_finite ℚ a)
  obtain ⟨y, hy, hint⟩ := hz.exists_integral_multiple
  refine ⟨y.natAbs, Int.natAbs_pos.mpr hy, ?_⟩
  rw [zsmul_eq_mul] at hint
  rcases Int.natAbs_eq y with h | h
  · have : ((y.natAbs : ℕ) : E) = (y : E) := by
      conv_rhs => rw [h]
      simp
    rw [this]; exact hint
  · have : ((y.natAbs : ℕ) : E) = -(y : E) := by
      conv_rhs => rw [h]
      simp
    rw [this, neg_mul]; exact hint.neg

theorem main : ∀ {E : Type} [inst : Field E] [NumberField E] {r : ℕ}
    (Λ : Submodule (NumberField.RingOfIntegers E) (Fin r → E)),
    Submodule.span E (↑Λ : Set (Fin r → E)) = ⊤ →
    ∀ (w : Fin r → E), ∃ (k : ℕ), (0 : ℕ) < k ∧ (↑k : E) • w ∈ Λ := by
  intro E _ _ r Λ hspan w
  have hw : w ∈ Submodule.span E (↑Λ : Set (Fin r → E)) := by rw [hspan]; trivial

  have hnat : ∀ (n : ℕ) (v : Fin r → E), v ∈ Λ → (n : E) • v ∈ Λ := by
    intro n v hv
    rw [Nat.cast_smul_eq_nsmul]
    exact Λ.nsmul_mem hv n
  induction hw using Submodule.span_induction with
  | mem x hx => exact ⟨1, one_pos, by simpa using hx⟩
  | zero => exact ⟨1, one_pos, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨k₁, hk₁, h₁⟩ := hx
    obtain ⟨k₂, hk₂, h₂⟩ := hy
    refine ⟨k₁ * k₂, Nat.mul_pos hk₁ hk₂, ?_⟩
    have e : ((k₁ * k₂ : ℕ) : E) • (x + y) = (k₂ : E) • ((k₁ : E) • x) + (k₁ : E) • ((k₂ : E) • y) := by
      rw [smul_add, smul_smul, smul_smul]; push_cast; ring_nf
    rw [e]
    exact Λ.add_mem (hnat _ _ h₁) (hnat _ _ h₂)
  | smul a x _ hx =>
    obtain ⟨k, hk, h⟩ := hx
    obtain ⟨d, hd, hint⟩ := exists_nat_mul_integral a
    refine ⟨d * k, Nat.mul_pos hd hk, ?_⟩
    let c : NumberField.RingOfIntegers E := ⟨(d : E) * a, hint⟩
    have e : ((d * k : ℕ) : E) • (a • x) = c • ((k : E) • x) := by
      funext i
      simp only [Pi.smul_apply, smul_eq_mul]
      rw [Algebra.smul_def]
      change _ = ((d : E) * a) * _
      push_cast; ring
    rw [e]
    exact Λ.smul_mem c h

end GlobalTheory.NatMulIntegralExists
