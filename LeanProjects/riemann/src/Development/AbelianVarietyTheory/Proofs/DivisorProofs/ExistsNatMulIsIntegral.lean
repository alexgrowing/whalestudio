import Mathlib

namespace GlobalTheory.NatMultipleIntegral

open NumberField

theorem exists_nat_mul_isIntegral (E : Type) [Field E] [NumberField E] (c : E) :
    ∃ n : ℕ, 0 < n ∧ IsIntegral ℤ ((n : E) * c) := by
  have h1 : IsAlgebraic ℚ c := Algebra.IsAlgebraic.isAlgebraic c
  have h2 : IsAlgebraic ℤ c := (IsFractionRing.isAlgebraic_iff ℤ ℚ E).mpr h1
  obtain ⟨y, hy, hint⟩ := h2.exists_integral_multiple
  refine ⟨y.natAbs, Int.natAbs_pos.mpr hy, ?_⟩
  rw [zsmul_eq_mul] at hint
  rcases Int.natAbs_eq y with h | h
  · have : ((y.natAbs : ℕ) : E) = (y : E) := by
      conv_rhs => rw [h]
      exact (Int.cast_natCast _).symm
    rw [this]; exact hint
  · have : ((y.natAbs : ℕ) : E) = -(y : E) := by
      conv_rhs => rw [h]
      rw [Int.cast_neg, neg_neg, Int.cast_natCast]
    rw [this, neg_mul]; exact hint.neg

theorem exists_nat_smul_mem (E : Type) [inst : Field E] [NumberField E] (r : ℕ)
    (Λ : Submodule (NumberField.RingOfIntegers E) (Fin r → E))
    (hΛ : Submodule.span E (↑Λ : Set (Fin r → E)) = ⊤) (v : Fin r → E) :
    ∃ (q : ℕ), (0 : ℕ) < q ∧ (↑q : E) • v ∈ Λ := by
  have hv : v ∈ Submodule.span E (↑Λ : Set (Fin r → E)) := hΛ ▸ Submodule.mem_top
  have key : ∀ (a : E), IsIntegral ℤ a → ∀ x ∈ Λ, a • x ∈ Λ := by
    intro a ha x hx
    exact Λ.smul_mem (⟨a, ha⟩ : NumberField.RingOfIntegers E) hx
  have keyn : ∀ (n : ℕ), ∀ x ∈ Λ, (n : E) • x ∈ Λ := by
    intro n x hx
    rw [Nat.cast_smul_eq_nsmul]
    exact nsmul_mem hx n
  induction hv using Submodule.span_induction with
  | mem x hx => exact ⟨1, one_pos, by simpa using hx⟩
  | zero => exact ⟨1, one_pos, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨p, hp, hpx⟩ := hx
    obtain ⟨q, hq, hqy⟩ := hy
    refine ⟨p * q, Nat.mul_pos hp hq, ?_⟩
    have e : ((p * q : ℕ) : E) • (x + y) = (q : E) • ((p : E) • x) + (p : E) • ((q : E) • y) := by
      rw [smul_add, smul_smul, smul_smul, Nat.cast_mul, mul_comm (q : E) (p : E)]
    rw [e]
    exact Λ.add_mem (keyn q _ hpx) (keyn p _ hqy)
  | smul c x _ hx =>
    obtain ⟨p, hp, hpx⟩ := hx
    obtain ⟨n, hn, hint⟩ := exists_nat_mul_isIntegral E c
    refine ⟨n * p, Nat.mul_pos hn hp, ?_⟩
    have e : ((n * p : ℕ) : E) • (c • x) = ((n : E) * c) • ((p : E) • x) := by
      rw [smul_smul, smul_smul, Nat.cast_mul]
      congr 1
      ring
    rw [e]
    exact key _ hint _ hpx

end GlobalTheory.NatMultipleIntegral
