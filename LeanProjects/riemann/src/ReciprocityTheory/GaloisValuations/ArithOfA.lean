import ReciprocityTheory.GaloisValuations.Global

noncomputable section

open NumberField IsDedekindDomain Pointwise

namespace ReciprocityTheory.Gal

open Formalism.ConjugateSelfDual

section deg

variable {F : Type*} [Field F] [NumberField F]

def locDegree (v : HeightOneSpectrum (𝓞 F)) : ℕ :=
  v.asIdeal.ramificationIdx ℤ * v.asIdeal.inertiaDeg ℤ

theorem isMaximal_span_prime (l : ℕ) [hl : Fact l.Prime] : (Ideal.span {(l : ℤ)}).IsMaximal := by
  first
    | exact PrincipalIdealRing.isMaximal_of_irreducible (Nat.prime_iff_prime_int.mp hl.out).irreducible
    | exact Ideal.IsPrime.isMaximal
        ((Ideal.span_singleton_prime (by exact_mod_cast hl.out.ne_zero)).2
          (Nat.prime_iff_prime_int.mp hl.out))
        (by simp [hl.out.ne_zero])

theorem liesOver_span_iff (l : ℕ) [Fact l.Prime] (P : Ideal (𝓞 F)) [P.IsPrime] :
    P.LiesOver (Ideal.span {(l : ℤ)}) ↔ ((l : ℕ) : 𝓞 F) ∈ P := by
  constructor
  · intro h
    have hmem : ((l : ℤ)) ∈ P.under ℤ := by
      rw [← h.over]
      exact Ideal.mem_span_singleton_self _
    have h2 : algebraMap ℤ (𝓞 F) (l : ℤ) ∈ P := hmem
    simpa using h2
  · intro h
    refine ⟨?_⟩
    refine (isMaximal_span_prime l).eq_of_le (Ideal.IsPrime.ne_top inferInstance) ?_
    rw [Ideal.span_le, Set.singleton_subset_iff]
    show algebraMap ℤ (𝓞 F) (l : ℤ) ∈ P
    simpa using h

theorem sum_locDegree (l : ℕ) [Fact l.Prime] (T : Finset (HeightOneSpectrum (𝓞 F)))
    (hT : ∀ v, v ∈ T ↔ ((l : ℕ) : 𝓞 F) ∈ v.asIdeal) :
    ∑ v ∈ T, locDegree v = Module.finrank ℚ F := by
  haveI := isMaximal_span_prime l
  have hl0 : (l : ℤ) ≠ 0 := by exact_mod_cast (Fact.out : l.Prime).ne_zero
  have hp0 : Ideal.span {(l : ℤ)} ≠ ⊥ := by
    rw [Ne, Ideal.span_singleton_eq_bot]
    exact hl0
  have h := Ideal.sum_ramification_inertia (𝓞 F) ℚ F hp0
  rw [← h]
  refine Finset.sum_nbij (fun v => v.asIdeal) ?_ ?_ ?_ ?_
  · intro v hv
    rw [IsDedekindDomain.mem_primesOverFinset_iff hp0 (𝓞 F)]
    haveI : v.asIdeal.LiesOver (Ideal.span {(l : ℤ)}) :=
      (liesOver_span_iff l v.asIdeal).2 ((hT v).1 hv)
    exact ⟨v.isPrime, inferInstance⟩
  · intro v _ w _ hvw
    exact HeightOneSpectrum.ext hvw
  · intro P hP
    rw [Finset.mem_coe, IsDedekindDomain.mem_primesOverFinset_iff hp0 (𝓞 F)] at hP
    obtain ⟨hPp, hPl⟩ := hP
    have hPne : P ≠ ⊥ := by
      intro hb
      have hm := (liesOver_span_iff l P).1 hPl
      rw [hb, Ideal.mem_bot] at hm
      exact (Fact.out : l.Prime).ne_zero (by exact_mod_cast hm)
    refine ⟨⟨P, hPp, hPne⟩, ?_, rfl⟩
    rw [Finset.mem_coe, hT]
    exact (liesOver_span_iff l P).1 hPl
  · intro v hv
    haveI : v.asIdeal.LiesOver (Ideal.span {(l : ℤ)}) :=
      (liesOver_span_iff l v.asIdeal).2 ((hT v).1 hv)
    haveI := v.isMaximal
    unfold locDegree
    rw [Ideal.ramificationIdx'_eq_ramificationIdx (Ideal.span {(l : ℤ)}) v.asIdeal hp0,
      Ideal.inertiaDeg'_eq_inertiaDeg (Ideal.span {(l : ℤ)}) v.asIdeal]

end deg

section conj

variable {F Ω : Type*} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω]

theorem smul_valuation_le_one_iff (γ : G F Ω) (A : ValuationSubring Ω) (y : Ω) :
    (γ • A).valuation y ≤ 1 ↔ A.valuation ((γ⁻¹ : G F Ω) y) ≤ 1 := by
  rw [ValuationSubring.valuation_le_one_iff, ValuationSubring.valuation_le_one_iff,
    ValuationSubring.mem_smul_pointwise_iff_exists]
  constructor
  · rintro ⟨s, hs, rfl⟩
    show γ⁻¹ • γ • s ∈ A
    rwa [inv_smul_smul]
  · intro h
    exact ⟨γ⁻¹ • y, h, smul_inv_smul γ y⟩

private theorem smul_valuationSubring_valuation_lt_one_iff (γ : G F Ω) (A : ValuationSubring Ω) (y : Ω) :
    (γ • A).valuation y < 1 ↔ A.valuation ((γ⁻¹ : G F Ω) y) < 1 := by
  by_cases hy : y = 0
  · simp [hy]
  · have hy' : (γ⁻¹ : G F Ω) y ≠ 0 := (map_ne_zero (γ⁻¹ : G F Ω)).2 hy
    rw [Valuation.val_lt_one_iff _ hy, Valuation.val_lt_one_iff _ hy', ← not_le, ← not_le,
      smul_valuation_le_one_iff, map_inv₀]

theorem conj_mem_Ine_smul {A : ValuationSubring Ω} {γ σ : G F Ω} (hσ : σ ∈ Ine (F := F) A) :
    γ * σ * γ⁻¹ ∈ Ine (F := F) (γ • A) := by
  obtain ⟨hσ1, hσ2⟩ := hσ
  show γ * σ * γ⁻¹ ∈ Inertia (F := F) (γ • A)
  refine ⟨?_, fun x hx => ?_⟩
  · have h1 : σ • A = A := hσ1
    show (γ * σ * γ⁻¹) • (γ • A) = γ • A
    rw [mul_smul, mul_smul, inv_smul_smul, h1]
  · rw [smul_valuation_le_one_iff] at hx
    rw [smul_valuationSubring_valuation_lt_one_iff]
    have e : (γ⁻¹ : G F Ω) ((γ * σ * γ⁻¹) x - x) =
        σ ((γ⁻¹ : G F Ω) x) - (γ⁻¹ : G F Ω) x := by
      rw [map_sub]
      congr 1
      show (γ⁻¹ : G F Ω) (γ (σ ((γ⁻¹ : G F Ω) x))) = σ ((γ⁻¹ : G F Ω) x)
      first | exact γ.symm_apply_apply _ | simp
    rw [e]
    exact hσ2 _ hx

end conj

end ReciprocityTheory.Gal
