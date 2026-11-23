import Mathlib

theorem UpperTheory.Reformulated.B.Qk41.precomplete_of_pow_le :
    ∀ {A : Type} [inst : CommRing A]
    {I J : Ideal A}, J ≤ I → ∀ {e : ℕ}, I ^ e ≤ J → ∀ [IsPrecomplete J A], IsPrecomplete I A := by
  intro A _ I J hJI e he hJ
  refine ⟨fun f hf => ?_⟩
  have h1 : ∀ m : ℕ, I ^ ((e + 1) * m) ≤ J ^ m := fun m => by
    rw [pow_mul]
    exact Ideal.pow_right_mono ((Ideal.pow_le_pow_right (Nat.le_succ e)).trans he) m
  obtain ⟨L, hL⟩ := IsPrecomplete.prec hJ (f := fun n => f ((e + 1) * n)) (fun {m n} hmn =>
    SModEq.mono (Submodule.smul_mono_left (h1 m)) (hf (Nat.mul_le_mul_left _ hmn)))
  refine ⟨L, fun n => ?_⟩
  exact (hf (Nat.le_mul_of_pos_left n (Nat.succ_pos e))).trans
    (SModEq.mono (Submodule.smul_mono_left (Ideal.pow_right_mono hJI n)) (hL n))
