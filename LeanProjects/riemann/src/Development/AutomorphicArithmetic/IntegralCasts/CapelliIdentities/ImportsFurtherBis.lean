import Mathlib

theorem UpperTheory.Reformulated.B.Qk57.eval₂_scale.{u_1, u_2} :
    ∀ {A : Type u_1} {S : Type u_2} [inst : CommRing A] [inst_1 : CommRing S] {n : ℕ} (g : A →+* S) (x : Fin n → S)
    (w : S) {m : ℕ} {a : MvPolynomial (Fin n) A},
    a.IsHomogeneous m → MvPolynomial.eval₂ g (fun (l : Fin n) ↦ w * x l) a = w ^ m * MvPolynomial.eval₂ g x a := by
  intro A S _ _ n g x w m a h
  rw [MvPolynomial.eval₂_eq', MvPolynomial.eval₂_eq', Finset.mul_sum]
  refine Finset.sum_congr rfl fun d hd => ?_
  have hdeg : ∑ i, d i = m := by
    have h1 := h (MvPolynomial.mem_support_iff.mp hd)
    rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by simp)] at h1
    simpa using h1
  simp only [mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, hdeg]
  ring
