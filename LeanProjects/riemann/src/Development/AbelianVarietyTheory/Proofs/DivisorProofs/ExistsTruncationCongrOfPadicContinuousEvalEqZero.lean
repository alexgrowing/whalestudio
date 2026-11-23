import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd

open GlobalTheory.QLog

namespace GlobalTheory

theorem evalPoly_eq {O A : Type} [CommRing O] [CommRing A] [Algebra O A] {d : ℕ}
    (x : Fin d → A) (E : MvPowerSeries (Fin d) O →ₐ[O] A) (hX : ∀ i, E (MvPowerSeries.X i) = x i)
    (P : MvPolynomial (Fin d) O) : E (P : MvPowerSeries (Fin d) O) = MvPolynomial.aeval x P := by
  have key : E.comp (MvPolynomial.coeToMvPowerSeries.algHom O) = MvPolynomial.aeval x :=
    MvPolynomial.algHom_ext fun i => by simp [hX]
  have := congrArg (fun F : MvPolynomial (Fin d) O →ₐ[O] A => F P) key
  simpa using this

theorem aeval_monomial_mem_span_pow {O A : Type} [CommRing O] [CommRing A] [Algebra O A] {d : ℕ}
    (x : Fin d → A) (N : ℕ) (α : Fin d →₀ ℕ) (hα : N ≤ α.degree) (c : O) :
    MvPolynomial.aeval x (MvPolynomial.monomial α c) ∈ Ideal.span (Set.range x) ^ N := by
  rw [MvPolynomial.aeval_monomial]
  refine Ideal.mul_mem_left _ _ (Ideal.pow_le_pow_right hα ?_)
  rw [Finsupp.degree_apply, ← Finset.prod_pow_eq_pow_sum]
  exact Ideal.prod_mem_prod fun i _ => Ideal.pow_mem_pow (Ideal.subset_span (Set.mem_range_self i)) _

end GlobalTheory

namespace GlobalTheory

theorem trunc_dec : ∀ (p : ℕ) (O A : Type) [CommRing O] [CommRing A] [Algebra O A] (d : ℕ) (x : Fin d → A) (E : MvPowerSeries (Fin d) O →ₐ[O] A), IsEval p x E → ∀ (n N : ℕ) (f : MvPowerSeries (Fin d) O), E f = 0 → ∃ P : MvPolynomial (Fin d) O, (∀ α : Fin d →₀ ℕ, N ≤ α.degree → MvPolynomial.coeff α P = 0) ∧ (∀ α : Fin d →₀ ℕ, α.degree < N → MvPolynomial.coeff α P = MvPowerSeries.coeff α f) ∧ MvPolynomial.aeval x P ∈ Ideal.span (Set.range x) ^ N ⊔ Ideal.span {(p : A) ^ n} := by
  intro p O A _ _ _ d x E hE n N f hf
  obtain ⟨hX, hc⟩ := hE
  obtain ⟨M, hM⟩ := hc n
  classical
  set F : Finset (Fin d →₀ ℕ) := Finset.Iic (Finsupp.equivFunOnFinite.symm fun _ => max N M) with hF
  have memF : ∀ α : Fin d →₀ ℕ, α.degree < max N M → α ∈ F := by
    intro α h
    rw [hF, Finset.mem_Iic]
    intro i
    simpa using (Finsupp.le_degree i α).trans h.le
  set P : MvPolynomial (Fin d) O :=
    ∑ α ∈ F.filter (fun α => α.degree < N), MvPolynomial.monomial α (MvPowerSeries.coeff α f) with hP
  set Q : MvPolynomial (Fin d) O :=
    ∑ α ∈ F.filter (fun α => ¬ α.degree < N), MvPolynomial.monomial α (MvPowerSeries.coeff α f) with hQ
  have cP : ∀ β, MvPolynomial.coeff β P = if β ∈ F ∧ β.degree < N then MvPowerSeries.coeff β f else 0 := by
    intro β
    rw [hP, MvPolynomial.coeff_sum]
    simp only [MvPolynomial.coeff_monomial]
    rw [Finset.sum_ite_eq' (F.filter _) β]
    simp only [Finset.mem_filter]
  have cQ : ∀ β, MvPolynomial.coeff β Q = if β ∈ F ∧ ¬ β.degree < N then MvPowerSeries.coeff β f else 0 := by
    intro β
    rw [hQ, MvPolynomial.coeff_sum]
    simp only [MvPolynomial.coeff_monomial]
    rw [Finset.sum_ite_eq' (F.filter _) β]
    simp only [Finset.mem_filter]
  refine ⟨P, ?_, ?_, ?_⟩
  · intro α hα
    rw [cP, if_neg]
    omega
  · intro α hα
    rw [cP, if_pos ⟨memF α (lt_of_lt_of_le hα (le_max_left _ _)), hα⟩]
  · have hrest : (p : A) ^ n ∣ E (f - (P : MvPowerSeries (Fin d) O) - (Q : MvPowerSeries (Fin d) O)) := by
      apply hM
      intro α hα
      have hαF := memF α (lt_of_lt_of_le hα (le_max_right _ _))
      rw [map_sub, map_sub, MvPolynomial.coeff_coe, MvPolynomial.coeff_coe, cP, cQ]
      by_cases h : α.degree < N
      · simp [hαF, h]
      · simp [hαF, h]
    have hQmem : MvPolynomial.aeval x Q ∈ Ideal.span (Set.range x) ^ N := by
      rw [hQ, map_sum]
      refine Ideal.sum_mem _ fun α hα => aeval_monomial_mem_span_pow x N α ?_ _
      exact not_lt.1 (Finset.mem_filter.1 hα).2
    have hsplit : MvPolynomial.aeval x P = -(MvPolynomial.aeval x Q) -
        E (f - (P : MvPowerSeries (Fin d) O) - (Q : MvPowerSeries (Fin d) O)) := by
      rw [map_sub, map_sub, hf, evalPoly_eq x E hX, evalPoly_eq x E hX]
      ring
    rw [hsplit]
    refine Ideal.sub_mem _ ((Ideal.neg_mem_iff _).2 (Ideal.mem_sup_left hQmem)) (Ideal.mem_sup_right ?_)
    exact Ideal.mem_span_singleton.2 hrest

end GlobalTheory
