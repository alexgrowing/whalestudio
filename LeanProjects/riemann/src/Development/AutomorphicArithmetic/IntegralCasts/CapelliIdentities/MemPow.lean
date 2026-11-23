import Mathlib

namespace PrecompleteLimitOfPowDvd

private lemma memPow {R : Type*} [CommRing R] (π x : R) (m : ℕ) :
    x ∈ ((Ideal.span {π}) ^ m • (⊤ : Submodule R R)) ↔ π ^ m ∣ x := by
  rw [smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow, Ideal.mem_span_singleton]

private lemma tele {R : Type*} [CommRing R] (π : R) (f : ℕ → R)
    (h : ∀ n : ℕ, π ^ n ∣ f (n + 1) - f n) (m : ℕ) : ∀ k : ℕ, π ^ m ∣ f (m + k) - f m := by
  intro k
  induction k with
  | zero => simp
  | succ k ih =>
    have h2 : π ^ m ∣ f (m + k + 1) - f (m + k) :=
      (pow_dvd_pow π (Nat.le_add_right m k)).trans (h (m + k))
    have : f (m + (k + 1)) - f m = (f (m + k + 1) - f (m + k)) + (f (m + k) - f m) := by
      rw [← add_assoc]; ring
    rw [this]; exact dvd_add h2 ih

end PrecompleteLimitOfPowDvd

theorem UpperTheory.Reformulated.B.Yra6.main.{u_1} :
    ∀ {R : Type u_1} [inst : CommRing R] {π : R},
      IsPrecomplete (Ideal.span {π}) R →
        ∀ (f : ℕ → R), (∀ (n : ℕ), π ^ n ∣ f (n + (1 : ℕ)) - f n) → ∃ (L : R), ∀ (n : ℕ), π ^ n ∣ f n - L := by
  intro R _ π hP f h
  obtain ⟨L, hL⟩ := hP.prec' f (by
    intro m n hmn
    rw [SModEq.sub_mem, PrecompleteLimitOfPowDvd.memPow]
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hmn
    have := PrecompleteLimitOfPowDvd.tele π f h m k
    rw [← neg_sub]; exact (dvd_neg).2 this)
  refine ⟨L, fun n => ?_⟩
  have := hL n
  rw [SModEq.sub_mem, PrecompleteLimitOfPowDvd.memPow] at this
  exact this
