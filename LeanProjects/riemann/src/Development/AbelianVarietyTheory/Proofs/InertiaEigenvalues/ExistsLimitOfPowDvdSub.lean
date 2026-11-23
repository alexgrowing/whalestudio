import Mathlib

namespace GlobalTheory.LimitOfDivisibility

theorem exists_limit_of_pow_dvd_sub {R : Type} [inst : CommRing R] (p : ℕ)
    [IsAdicComplete (Ideal.span {(↑p : R)}) R] (f : ℕ → R)
    (h : ∀ (n : ℕ), (↑p : R) ^ n ∣ f (n + (1 : ℕ)) - f n) :
    ∃ (L : R), ∀ (n : ℕ), (↑p : R) ^ n ∣ L - f n := by
  have key : ∀ (n : ℕ) (x y : R),
      x ≡ y [SMOD ((Ideal.span {(p : R)}) ^ n • ⊤ : Submodule R R)] ↔ (p : R) ^ n ∣ x - y := by
    intro n x y
    rw [SModEq.sub_mem, Ideal.smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow,
      Ideal.mem_span_singleton]
  have hc : ∀ m k : ℕ, (p : R) ^ m ∣ f (m + k) - f m := by
    intro m k
    induction k with
    | zero => simp
    | succ k ih =>
      have h1 : (p : R) ^ m ∣ f (m + k + 1) - f (m + k) :=
        (pow_dvd_pow _ (Nat.le_add_right m k)).trans (h (m + k))
      have h2 := dvd_add h1 ih
      have e : f (m + k + 1) - f (m + k) + (f (m + k) - f m) = f (m + (k + 1)) - f m := by
        rw [← Nat.add_assoc]; ring
      rwa [e] at h2
  obtain ⟨L, hL⟩ := IsPrecomplete.prec (I := Ideal.span {(p : R)}) (M := R) inferInstance (f := f) (by
    intro m n hmn
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hmn
    rw [key, dvd_sub_comm]
    exact hc m k)
  refine ⟨L, fun n => ?_⟩
  rw [dvd_sub_comm]
  exact (key n _ _).1 (hL n)

end GlobalTheory.LimitOfDivisibility
