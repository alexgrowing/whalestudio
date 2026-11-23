import Mathlib
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModGDefs
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModGBasic

noncomputable section
open scoped BigOperators Classical UpperHalfPlane
open NumberField IsDedekindDomain Formalism.L2.Th1.CM Neutral.HilbertClassField

namespace ReciprocityTheory.ChartRestriction.L1

theorem exists_int_multiple {Ω : Type*} [Field Ω] [CharZero Ω] {β : Ω} (hβ : IsIntegral ℤ β) (h0 : β ≠ 0) :
    ∃ (n : ℤ) (γ : Ω), n ≠ 0 ∧ IsIntegral ℤ γ ∧ (n : Ω) = β * γ := by
  obtain ⟨p, hpm, hp0⟩ := id hβ
  obtain ⟨q, hpq, hq⟩ := Polynomial.exists_eq_pow_rootMultiplicity_mul_and_not_dvd p hpm.ne_zero 0
  simp only [map_zero, sub_zero] at hpq hq
  have hq0 : q.coeff 0 ≠ 0 := fun h => hq (Polynomial.X_dvd_iff.2 h)
  have haq : Polynomial.aeval β q = 0 := by
    have h1 : Polynomial.aeval β p = 0 := by rw [Polynomial.aeval_def]; exact hp0
    rw [hpq, map_mul, map_pow, Polynomial.aeval_X] at h1
    exact (mul_eq_zero.1 h1).resolve_left (pow_ne_zero _ h0)
  refine ⟨q.coeff 0, -(Polynomial.aeval β q.divX), hq0, ?_, ?_⟩
  · have hmem := adjoin_le_integralClosure hβ (Polynomial.aeval_mem_adjoin_singleton ℤ β (p := q.divX))
    exact (neg_mem hmem : _ ∈ integralClosure ℤ Ω)
  · have h2 := congrArg (Polynomial.aeval β) (Polynomial.divX_mul_X_add q)
    rw [map_add, map_mul, Polynomial.aeval_X, Polynomial.aeval_C, haq, eq_intCast] at h2
    linear_combination h2

theorem mem_valuationSubring_of_isIntegral {Ω : Type*} [Field Ω] {x : Ω} (hx : IsIntegral ℤ x)
    (A : ValuationSubring Ω) : x ∈ A := by
  have hA : IsIntegral A x := hx.tower_top
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.1 hA
  rw [← hy]
  exact y.2

theorem sepInt {Ω : Type*} [Field Ω] [CharZero Ω] (s : Finset Ω) (hs : ∀ r ∈ s, IsIntegral ℤ r) :
    ∃ n : ℤ, n ≠ 0 ∧ ∀ r ∈ s, ∀ r' ∈ s, r ≠ r' → ∀ A : ValuationSubring Ω, r - r' ∈ A.nonunits →
      (n : Ω) ∈ A.nonunits := by
  classical
  have key : ∀ q ∈ s.offDiag, ∃ (m : ℤ) (γ : Ω), m ≠ 0 ∧ IsIntegral ℤ γ ∧ (m : Ω) = (q.1 - q.2) * γ := by
    intro q hq
    rw [Finset.mem_offDiag] at hq
    exact exists_int_multiple ((hs _ hq.1).sub (hs _ hq.2.1)) (sub_ne_zero.2 hq.2.2)
  choose! m γ hm hγ hmγ using key
  refine ⟨∏ q ∈ s.offDiag, m q, Finset.prod_ne_zero_iff.2 hm, ?_⟩
  intro r hr r' hr' hne A hA
  have hq : (r, r') ∈ s.offDiag := Finset.mem_offDiag.2 ⟨hr, hr', hne⟩
  rw [Int.cast_prod, ← Finset.mul_prod_erase _ _ hq]
  rw [ValuationSubring.mem_nonunits_iff] at hA ⊢
  rw [Valuation.map_mul, hmγ _ hq, Valuation.map_mul]
  have h1 : A.valuation (γ (r, r')) ≤ 1 :=
    (A.valuation_le_one_iff _).2 (mem_valuationSubring_of_isIntegral (hγ _ hq) A)
  have h2 : A.valuation (∏ q ∈ s.offDiag.erase (r, r'), (m q : Ω)) ≤ 1 :=
    (A.valuation_le_one_iff _).2 (prod_mem fun q _ => intCast_mem _ _)
  calc _ ≤ A.valuation (r - r') * 1 * 1 := mul_le_mul' (mul_le_mul' le_rfl h1) h2
    _ < 1 := by rw [mul_one, mul_one]; exact hA

theorem finite_places (E : Type*) [Field E] [NumberField E] {n : ℤ} (hn : n ≠ 0) :
    {v : HeightOneSpectrum (𝓞 E) | (n : 𝓞 E) ∈ v.asIdeal}.Finite := by
  have hI : Ideal.span {(n : 𝓞 E)} ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact_mod_cast hn
  refine (Ideal.finite_factors hI).subset fun v hv => ?_
  simp only [Set.mem_setOf_eq] at hv ⊢
  rw [Ideal.dvd_iff_le, Ideal.span_singleton_le_iff_mem]
  exact hv

end ReciprocityTheory.ChartRestriction.L1
