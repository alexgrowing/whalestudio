import Mathlib

namespace GlobalTheory.SplittingAdditive

open BigOperators

def Splits {G : Type} [Mul G] (A : Subalgebra ℂ (G → ℂ)) (p : G → ℂ) : Prop :=
  ∃ (m : ℕ) (a : Fin m → G → ℂ) (b : Fin m → G → ℂ),
    (∀ i : Fin m, a i ∈ A ∧ b i ∈ A) ∧ ∀ x k : G, p (x * k) = ∑ i : Fin m, a i x * b i k

theorem splits_add {G : Type} [Mul G] (A : Subalgebra ℂ (G → ℂ)) {p q : G → ℂ}
    (hp : Splits A p) (hq : Splits A q) : Splits A (p + q) := by
  obtain ⟨m, a, b, hab, h⟩ := hp
  obtain ⟨n, c, d, hcd, h'⟩ := hq
  refine ⟨m + n, Fin.append a c, Fin.append b d, ?_, ?_⟩
  · intro i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simpa using hab j
    · simpa using hcd j
  · intro x k
    rw [Fin.sum_univ_add]
    simp [h, h']

theorem splits_mul {G : Type} [Mul G] (A : Subalgebra ℂ (G → ℂ)) {p q : G → ℂ}
    (hp : Splits A p) (hq : Splits A q) : Splits A (p * q) := by
  obtain ⟨m, a, b, hab, h⟩ := hp
  obtain ⟨n, c, d, hcd, h'⟩ := hq
  let e : Fin m × Fin n ≃ Fin (m * n) := finProdFinEquiv
  refine ⟨m * n, fun j => a (e.symm j).1 * c (e.symm j).2,
    fun j => b (e.symm j).1 * d (e.symm j).2, ?_, ?_⟩
  · intro j
    exact ⟨A.mul_mem (hab _).1 (hcd _).1, A.mul_mem (hab _).2 (hcd _).2⟩
  · intro x k
    have key : ∀ f : Fin m × Fin n → ℂ, ∑ j : Fin (m * n), f (e.symm j) = ∑ q, f q :=
      fun f => Equiv.sum_comp e.symm f
    simp only [Pi.mul_apply]
    rw [key (fun q => a q.1 x * c q.2 x * (b q.1 k * d q.2 k)), h, h', Finset.sum_mul_sum,
      Fintype.sum_prod_type]
    refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
    ring

theorem splits_algebraMap {G : Type} [Mul G] (A : Subalgebra ℂ (G → ℂ)) (r : ℂ) :
    Splits A (algebraMap ℂ (G → ℂ) r) := by
  refine ⟨1, fun _ => algebraMap ℂ (G → ℂ) r, fun _ => 1, ?_, ?_⟩
  · intro _
    exact ⟨A.algebraMap_mem r, A.one_mem⟩
  · intro x k
    simp

theorem main :
    ∀ {G : Type} [inst : Mul G] (S : Set (G → ℂ)),
      (∀ p ∈ S, ∃ (m : ℕ) (a : Fin m → G → ℂ) (b : Fin m → G → ℂ),
        (∀ (i : Fin m), a i ∈ Algebra.adjoin ℂ S ∧ b i ∈ Algebra.adjoin ℂ S) ∧
          ∀ (x k : G), p (x * k) = ∑ i : Fin m, a i x * b i k) →
      ∀ p ∈ Algebra.adjoin ℂ S, ∃ (m : ℕ) (a : Fin m → G → ℂ) (b : Fin m → G → ℂ),
        (∀ (i : Fin m), a i ∈ Algebra.adjoin ℂ S ∧ b i ∈ Algebra.adjoin ℂ S) ∧
          ∀ (x k : G), p (x * k) = ∑ i : Fin m, a i x * b i k := by
  intro G _ S hS p hp
  change Splits (Algebra.adjoin ℂ S) p
  induction hp using Algebra.adjoin_induction with
  | mem x hx => exact hS x hx
  | algebraMap r => exact splits_algebraMap _ r
  | add x y _ _ hx hy => exact splits_add _ hx hy
  | mul x y _ _ hx hy => exact splits_mul _ hx hy

end GlobalTheory.SplittingAdditive
