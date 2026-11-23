import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd

set_option autoImplicit false

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog

namespace GlobalTheory.BinomLeft

variable {R : Type} [CommRing R] {d : ℕ}

theorem natCast_eq_monomial {σ : Type} (n : ℕ) : ((n : ℕ) : MvPowerSeries σ R) = monomial 0 (n : R) := by
  rw [monomial_zero_eq_C_apply, map_natCast]

theorem pow_threeGroupsFirst_add_second_expansion (i : Fin d) (k : ℕ) :
    ((x1 i + x2 i : MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) R)) ^ k =
      ∑ j ∈ Finset.range (k + 1),
        monomial (Finsupp.single (Sum.inl i) j + Finsupp.single (Sum.inr (Sum.inl i)) (k - j)) (k.choose j : R) := by
  rw [add_pow]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [x1, x2, X_pow_eq, monomial_mul_monomial, one_mul, natCast_eq_monomial, add_zero, mul_one]

theorem expo_iff (α : Fin d ⊕ Fin d →₀ ℕ) (a b e : Fin d →₀ ℕ) (p : Fin d → ℕ)
    (hp : ∀ i, p i ≤ α (Sum.inl i)) :
    Finsupp.sumElim a (Finsupp.sumElim b e) =
        (∑ i, (Finsupp.single (Sum.inl i) (p i) + Finsupp.single (Sum.inr (Sum.inl i)) (α (Sum.inl i) - p i))) +
          ∑ i, Finsupp.single (Sum.inr (Sum.inr i)) (α (Sum.inr i)) ↔
      α = Finsupp.sumElim (a + b) e ∧ p = ⇑a := by
  classical
  have hv : ∀ s, ((∑ i, (Finsupp.single (Sum.inl i) (p i) + Finsupp.single (Sum.inr (Sum.inl i)) (α (Sum.inl i) - p i))) +
          ∑ i, Finsupp.single (Sum.inr (Sum.inr i)) (α (Sum.inr i)) : Fin d ⊕ (Fin d ⊕ Fin d) →₀ ℕ) s =
        Sum.elim p (Sum.elim (fun i => α (Sum.inl i) - p i) (fun i => α (Sum.inr i))) s := by
    intro s
    rcases s with i | i | i
    · simp [Finsupp.finsetSum_apply, Finsupp.single_apply]
    · simp only [Finsupp.coe_add, Pi.add_apply, Finsupp.finsetSum_apply, Finsupp.single_apply]
      rw [Finset.sum_eq_single i (fun j _ hj => by simp [hj, Ne.symm hj]) (by simp)]
      simp
    · simp [Finsupp.finsetSum_apply, Finsupp.single_apply]
  constructor
  · intro h
    have h1 : ∀ i, a i = p i := fun i => by
      have := DFunLike.congr_fun h (Sum.inl i); rw [hv] at this; simpa using this
    have h2 : ∀ i, b i = α (Sum.inl i) - p i := fun i => by
      have := DFunLike.congr_fun h (Sum.inr (Sum.inl i)); rw [hv] at this; simpa using this
    have h3 : ∀ i, e i = α (Sum.inr i) := fun i => by
      have := DFunLike.congr_fun h (Sum.inr (Sum.inr i)); rw [hv] at this; simpa using this
    refine ⟨?_, funext fun i => (h1 i).symm⟩
    ext s
    rcases s with i | i
    · have := hp i; have := h1 i; have := h2 i; simp; omega
    · simp [h3 i]
  · rintro ⟨rfl, rfl⟩
    ext s
    rw [hv]
    rcases s with i | i | i <;> simp

theorem coeff_prod_pow_add (α : Fin d ⊕ Fin d →₀ ℕ) (a b e : Fin d →₀ ℕ) :
    coeff (Finsupp.sumElim a (Finsupp.sumElim b e))
        (α.prod fun s k => (Sum.elim (fun i => (x1 i + x2 i : MvPowerSeries (Fin d ⊕ (Fin d ⊕ Fin d)) R)) x3 s) ^ k) =
      if α = Finsupp.sumElim (a + b) e then (∏ i, ((a + b) i).choose (a i) : R) else 0 := by
  classical
  rw [Finsupp.prod_fintype _ _ (fun _ => pow_zero _), Fintype.prod_sum_type]
  simp only [Sum.elim_inl, Sum.elim_inr, pow_threeGroupsFirst_add_second_expansion]
  rw [Finset.prod_univ_sum]
  simp only [x3, X_pow_eq, prod_monomial, Finset.sum_mul, monomial_mul_monomial, mul_one, map_sum,
    coeff_monomial, Finset.prod_const_one]
  have hmem : ∀ p ∈ Fintype.piFinset fun i => Finset.range (α (Sum.inl i) + 1), ∀ i, p i ≤ α (Sum.inl i) := by
    intro p hp i
    have := Fintype.mem_piFinset.1 hp i
    rw [Finset.mem_range] at this
    omega
  split_ifs with hα
  · rw [Finset.sum_congr rfl fun p hp => by rw [if_congr (expo_iff α a b e p (hmem p hp)) rfl rfl]]
    simp only [hα, true_and]
    rw [Finset.sum_ite_eq']
    rw [if_pos]
    · simp
    · rw [Fintype.mem_piFinset]
      intro i
      simp only [Finset.mem_range, Finsupp.sumElim_apply, Sum.elim_inl, Finsupp.coe_add, Pi.add_apply]
      omega
  · refine Finset.sum_eq_zero fun p hp => ?_
    rw [if_neg]
    intro h
    exact hα ((expo_iff α a b e p (hmem p hp)).1 h).1

end GlobalTheory.BinomLeft
