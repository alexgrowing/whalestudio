import Mathlib

namespace GlobalTheory.TraceMulVanishing

theorem trace_mul_eq_zero_imp {F A : Type} [Field F] [CharZero F] [CommRing A] [Algebra F A]
    [Module.Finite F A] [IsReduced A] (x : A)
    (h : ∀ z : A, (Algebra.trace F A : A → F) (x * z) = (0 : F)) : x = 0 := by
  haveI : IsArtinianRing A := IsArtinianRing.of_finite F A
  obtain ⟨n, y, hy⟩ := IsArtinian.exists_pow_succ_smul_dvd x (1 : A)
  simp only [smul_eq_mul, mul_one] at hy

  have h1 : x ^ (n + 1) = x ^ (n + 1) * (x * y) := by
    calc x ^ (n + 1) = x * x ^ n := by rw [pow_succ']
      _ = x * (x ^ (n + 1) * y) := by rw [hy]
      _ = x ^ (n + 1) * (x * y) := by ring
  have h2 : ∀ j : ℕ, x ^ (n + 1) = x ^ (n + 1) * (x * y) ^ j := by
    intro j
    induction j with
    | zero => simp
    | succ j ih => rw [pow_succ (x * y) j, ← mul_assoc, ← ih]; exact h1
  have h3 : x ^ (n + 1) = x ^ (n + 1) * x ^ (n + 1) * y ^ (n + 1) := by
    calc x ^ (n + 1) = x ^ (n + 1) * (x * y) ^ (n + 1) := h2 (n + 1)
      _ = x ^ (n + 1) * x ^ (n + 1) * y ^ (n + 1) := by rw [mul_pow]; ring
  have he : IsIdempotentElem (x ^ (n + 1) * y ^ (n + 1)) := by
    unfold IsIdempotentElem
    calc x ^ (n + 1) * y ^ (n + 1) * (x ^ (n + 1) * y ^ (n + 1))
        = (x ^ (n + 1) * x ^ (n + 1) * y ^ (n + 1)) * y ^ (n + 1) := by ring
      _ = x ^ (n + 1) * y ^ (n + 1) := by rw [← h3]
  have htr : Algebra.trace F A (x ^ (n + 1) * y ^ (n + 1)) = 0 := by
    have := h (x ^ n * y ^ (n + 1))
    rwa [show x * (x ^ n * y ^ (n + 1)) = x ^ (n + 1) * y ^ (n + 1) by ring] at this
  have hl : IsIdempotentElem (Algebra.lmul F A (x ^ (n + 1) * y ^ (n + 1))) := he.map _
  have hz : Algebra.lmul F A (x ^ (n + 1) * y ^ (n + 1)) = 0 :=
    (LinearMap.IsIdempotentElem.trace_eq_zero_iff hl).1 (by rw [← Algebra.trace_apply]; exact htr)
  have he0 : x ^ (n + 1) * y ^ (n + 1) = 0 := by
    have := congrArg (fun f : Module.End F A => f 1) hz
    simpa using this
  have hxn : x ^ (n + 1) = 0 := by
    rw [h3, mul_assoc, he0, mul_zero]
  exact IsReduced.eq_zero x ⟨n + 1, hxn⟩

example : ∀ {F A : Type} [inst : Field F] [CharZero F] [inst_2 : CommRing A] [inst_3 : Algebra F A] [Module.Finite F A] [IsReduced A] (x : A), (∀ (z : A), (Algebra.trace F A : A → F) (x * z) = (0 : F)) → x = (0 : A) :=
  @trace_mul_eq_zero_imp

end GlobalTheory.TraceMulVanishing
