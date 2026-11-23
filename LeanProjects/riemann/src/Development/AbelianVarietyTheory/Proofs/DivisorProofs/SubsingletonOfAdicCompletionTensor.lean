import Mathlib
open TensorProduct

namespace GlobalTheory.AdicTorsion

variable {A : Type} [CommRing A] {f : A} {N : Type} [AddCommGroup N] [Module A N]

theorem pow_smul_eq_zero_of_le {n : N} {k j : ℕ} (hk : f ^ k • n = 0) (hkj : k ≤ j) :
    f ^ j • n = 0 := by
  rw [← pow_mul_pow_sub f hkj, mul_comm, mul_smul, hk, smul_zero]

theorem lift_smul_eq_of_le (x : AdicCompletion (Ideal.span {f}) A) {n : N} {k j : ℕ}
    (hk : f ^ k • n = 0) (hkj : k ≤ j) {a b : A}
    (ha : Submodule.Quotient.mk a = x.val k) (hb : Submodule.Quotient.mk b = x.val j) :
    a • n = b • n := by
  have h1 := x.property hkj
  rw [← hb, ← ha] at h1
  have h2 : b - a ∈ (Ideal.span {f} ^ k • ⊤ : Submodule A A) := by
    rw [← Submodule.Quotient.eq]
    simpa using h1
  rw [smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow, Ideal.mem_span_singleton] at h2
  obtain ⟨c, hc⟩ := h2
  have : (b - a) • n = 0 := by rw [hc, mul_comm, mul_smul, hk, smul_zero]
  rw [sub_smul, sub_eq_zero] at this
  exact this.symm

theorem lift_smul_eq (x : AdicCompletion (Ideal.span {f}) A) {n : N} {k j : ℕ}
    (hk : f ^ k • n = 0) (hj : f ^ j • n = 0) {a b : A}
    (ha : Submodule.Quotient.mk a = x.val k) (hb : Submodule.Quotient.mk b = x.val j) :
    a • n = b • n := by
  rcases le_total k j with h | h
  · exact lift_smul_eq_of_le x hk h ha hb
  · exact (lift_smul_eq_of_le x hj h hb ha).symm

variable (f) in

noncomputable def act (h : ∀ n : N, ∃ k : ℕ, f ^ k • n = 0)
    (x : AdicCompletion (Ideal.span {f}) A) (n : N) : N :=
  Classical.choose (Submodule.Quotient.mk_surjective _ (x.val (Classical.choose (h n)))) • n

theorem act_eq (h : ∀ n : N, ∃ k : ℕ, f ^ k • n = 0) (x : AdicCompletion (Ideal.span {f}) A)
    {n : N} {k : ℕ} (hk : f ^ k • n = 0) {a : A} (ha : Submodule.Quotient.mk a = x.val k) :
    act f h x n = a • n :=
  lift_smul_eq x (Classical.choose_spec (h n)) hk
    (Classical.choose_spec (Submodule.Quotient.mk_surjective _ _)) ha

variable (f) in

noncomputable def actBil (h : ∀ n : N, ∃ k : ℕ, f ^ k • n = 0) :
    AdicCompletion (Ideal.span {f}) A →ₗ[A] N →ₗ[A] N :=
  LinearMap.mk₂ A (act f h)
    (fun x y n => by
      obtain ⟨k, hk⟩ := h n
      obtain ⟨a, ha⟩ := Submodule.Quotient.mk_surjective _ (x.val k)
      obtain ⟨b, hb⟩ := Submodule.Quotient.mk_surjective _ (y.val k)
      rw [act_eq h x hk ha, act_eq h y hk hb, act_eq h (x + y) hk (a := a + b)
        (by rw [Submodule.Quotient.mk_add, ha, hb]; rfl), add_smul])
    (fun c x n => by
      obtain ⟨k, hk⟩ := h n
      obtain ⟨a, ha⟩ := Submodule.Quotient.mk_surjective _ (x.val k)
      rw [act_eq h x hk ha, act_eq h (c • x) hk (a := c * a)
        (by rw [← smul_eq_mul, Submodule.Quotient.mk_smul, ha]; rfl), mul_smul])
    (fun x n m => by
      obtain ⟨k₁, hk₁⟩ := h n
      obtain ⟨k₂, hk₂⟩ := h m
      have hn : f ^ (k₁ + k₂) • n = 0 := pow_smul_eq_zero_of_le hk₁ (Nat.le_add_right _ _)
      have hm : f ^ (k₁ + k₂) • m = 0 := pow_smul_eq_zero_of_le hk₂ (Nat.le_add_left _ _)
      have hnm : f ^ (k₁ + k₂) • (n + m) = 0 := by rw [smul_add, hn, hm, add_zero]
      obtain ⟨a, ha⟩ := Submodule.Quotient.mk_surjective _ (x.val (k₁ + k₂))
      rw [act_eq h x hn ha, act_eq h x hm ha, act_eq h x hnm ha, smul_add])
    (fun c x n => by
      obtain ⟨k, hk⟩ := h n
      have hc : f ^ k • (c • n) = 0 := by rw [smul_comm, hk, smul_zero]
      obtain ⟨a, ha⟩ := Submodule.Quotient.mk_surjective _ (x.val k)
      rw [act_eq h x hk ha, act_eq h x hc ha, smul_comm])

theorem act_of_one (h : ∀ n : N, ∃ k : ℕ, f ^ k • n = 0) (n : N) :
    act f h (AdicCompletion.of (Ideal.span {f}) A 1) n = n := by
  obtain ⟨k, hk⟩ := h n
  rw [act_eq h _ hk (a := 1) (by rw [AdicCompletion.of_apply]; rfl), one_smul]

end GlobalTheory.AdicTorsion

namespace GlobalTheory

theorem subsingleton_of_adicCompletion_tensor (A : Type) [CommRing A] (f : A) (N : Type)
    [AddCommGroup N] [Module A N] (h : ∀ n : N, ∃ k : ℕ, f ^ k • n = 0)
    (hT : Subsingleton (TensorProduct A (AdicCompletion (Ideal.span {f}) A) N)) :
    Subsingleton N := by
  refine ⟨fun n m => ?_⟩
  have key : ∀ n : N, n = 0 := fun n => by
    have e := congrArg (TensorProduct.lift (AdicTorsion.actBil f h))
      (Subsingleton.elim (AdicCompletion.of (Ideal.span {f}) A 1 ⊗ₜ[A] n) 0)
    rw [map_zero, TensorProduct.lift.tmul] at e
    simpa [AdicTorsion.actBil, AdicTorsion.act_of_one] using e
  rw [key n, key m]

example : ∀ (A : Type) [CommRing A] (f : A) (N : Type) [AddCommGroup N] [Module A N],
    (∀ n : N, ∃ k : ℕ, f ^ k • n = 0) →
    Subsingleton (TensorProduct A (AdicCompletion (Ideal.span {f}) A) N) → Subsingleton N :=
  @subsingleton_of_adicCompletion_tensor

end GlobalTheory
