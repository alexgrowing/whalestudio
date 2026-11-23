import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.NotIsTrDataGaussianIntOne

open GlobalTheory.AlmostEt

namespace GlobalTheory.AlmostEt

theorem derOn_killed_sq : ∀ (A S M : Type) [CommRing A] [CommRing S] [Algebra A S] [AddCommGroup M]
    [Module S M] (B C : Subalgebra A S) (tr : S → S) (n : ℕ) (a b : Fin n → S) (e : S),
    IsTrData B C tr a b e → ∀ D : S → M, IsDerOn C D → (∀ β ∈ B, D β = 0) →
      ∀ x ∈ C, (e * e) • D x = 0 := by
  intro A S M _ _ _ _ _ B C tr n a b e h D hD hB x hx
  have hsum : ∀ (s : Finset (Fin n)) (f : Fin n → S), (∀ i, f i ∈ C) →
      D (∑ i ∈ s, f i) = ∑ i ∈ s, D (f i) := by
    intro s f hf
    induction s using Finset.induction_on with
    | empty => simpa using hD.alg 0
    | insert j s hj ih =>
      rw [Finset.sum_insert hj, Finset.sum_insert hj,
        hD.add _ (hf j) _ (Subalgebra.sum_mem _ (fun i _ => hf i)), ih]
  have key : ∀ y ∈ C, e • D y = ∑ j, tr (b j * y) • D (a j) := by
    intro y hy
    have heC : e ∈ C := h.le h.e_mem
    have h1 : D (e * y) = e • D y := by
      rw [hD.mul e heC y hy, hB e h.e_mem, smul_zero, add_zero]
    rw [← h1, ← h.left y hy, hsum _ _ (fun j => C.mul_mem (h.a_mem j)
      (h.le (h.tr_mem _ (C.mul_mem (h.b_mem j) hy))))]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    have ht : tr (b j * y) ∈ B := h.tr_mem _ (C.mul_mem (h.b_mem j) hy)
    rw [hD.mul _ (h.a_mem j) _ (h.le ht), hB _ ht, smul_zero, zero_add]
  have L : ∑ i, b i • (e • D (x * a i)) = ∑ j, (e * x * b j) • D (a j) := by
    simp_rw [key _ (C.mul_mem hx (h.a_mem _)), Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [← Finset.sum_smul]
    congr 1
    have hr := h.right (b j * x) (C.mul_mem (h.b_mem j) hx)
    calc ∑ i, b i * tr (b j * (x * a i)) = ∑ i, b i * tr (a i * (b j * x)) := by
          refine Finset.sum_congr rfl (fun i _ => ?_)
          rw [show b j * (x * a i) = a i * (b j * x) by ring]
      _ = e * (b j * x) := hr
      _ = e * x * b j := by ring
  have R : ∑ i, b i • (e • D (x * a i)) = ∑ j, (e * x * b j) • D (a j) + (e * e) • D x := by
    simp_rw [hD.mul x hx _ (h.a_mem _), smul_add, smul_smul, Finset.sum_add_distrib,
      ← Finset.sum_smul]
    congr 1
    · refine Finset.sum_congr rfl (fun j _ => ?_)
      congr 1; ring
    · congr 1
      rw [show e * e = e * ∑ i, a i * b i by rw [h.sum], Finset.mul_sum]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      ring
  have := R.symm.trans L
  simpa using this

end GlobalTheory.AlmostEt
