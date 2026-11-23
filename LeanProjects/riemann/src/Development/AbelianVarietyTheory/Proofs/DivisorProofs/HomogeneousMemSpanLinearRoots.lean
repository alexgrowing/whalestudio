import Mathlib
import Formalism.DegreeFormula.FlagDegFormula

open MvPolynomial

namespace GlobalTheory

namespace PowLinSpan

variable {σ : Type} [Fintype σ] [DecidableEq σ]

theorem sum_C_mul_X_pow (u : σ → ℝ) (d : ℕ) :
    (∑ x, C (u x) * X x : MvPolynomial σ ℝ) ^ d =
      ∑ k ∈ Finset.piAntidiag Finset.univ d,
        ((Nat.multinomial Finset.univ k : ℝ) * ∏ x, u x ^ k x) •
          monomial (Finsupp.equivFunOnFinite.symm k) (1 : ℝ) := by
  rw [Finset.sum_pow_eq_sum_piAntidiag]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [smul_eq_C_mul, monomial_eq, Finsupp.prod_fintype _ _ (by simp)]
  simp only [mul_pow, Finset.prod_mul_distrib, ← map_pow, ← map_prod, map_mul, map_natCast, C_1, one_mul,
    Finsupp.coe_equivFunOnFinite_symm]
  ring

noncomputable def polOf (φ : Module.Dual ℝ (MvPolynomial σ ℝ)) (d : ℕ) : MvPolynomial σ ℝ :=
  ∑ k ∈ Finset.piAntidiag Finset.univ d,
    monomial (Finsupp.equivFunOnFinite.symm k)
      ((Nat.multinomial Finset.univ k : ℝ) * φ (monomial (Finsupp.equivFunOnFinite.symm k) 1))

theorem eval_polOf (φ : Module.Dual ℝ (MvPolynomial σ ℝ)) (d : ℕ) (u : σ → ℝ) :
    eval u (polOf φ d) = φ ((∑ x, C (u x) * X x) ^ d) := by
  rw [sum_C_mul_X_pow, map_sum, polOf, map_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [map_smul, eval_monomial, smul_eq_mul, Finsupp.prod_fintype _ _ (by simp)]
  simp only [Finsupp.coe_equivFunOnFinite_symm]
  ring

theorem coeff_polOf (φ : Module.Dual ℝ (MvPolynomial σ ℝ)) (d : ℕ) (m : σ →₀ ℕ) (hm : ∑ x, m x = d) :
    coeff m (polOf φ d) = (Nat.multinomial Finset.univ m : ℝ) * φ (monomial m 1) := by
  rw [polOf, coeff_sum]
  simp only [coeff_monomial]
  rw [Finset.sum_eq_single (⇑m)]
  · simp
  · intro k _ hk
    rw [if_neg]
    intro h
    apply hk
    rw [← h]
    simp
  · intro h
    exfalso
    apply h
    rw [Finset.mem_piAntidiag]
    simp [hm]

theorem degreeOf_polOf_le (φ : Module.Dual ℝ (MvPolynomial σ ℝ)) (d : ℕ) (x : σ) :
    (polOf φ d).degreeOf x ≤ d := by
  refine (degreeOf_le_totalDegree _ _).trans ?_
  refine (totalDegree_finset_sum _ _).trans (Finset.sup_le fun k hk => ?_)
  refine (totalDegree_monomial_le _ _).trans ?_
  rw [Finset.mem_piAntidiag] at hk
  rw [Finsupp.sum_fintype _ _ (by simp)]
  simpa [Finsupp.coe_equivFunOnFinite_symm] using hk.1.le

theorem monomial_kill (φ : Module.Dual ℝ (MvPolynomial σ ℝ)) (d : ℕ) (hP : polOf φ d = 0)
    (m : σ →₀ ℕ) (hm : ∑ x, m x = d) : φ (monomial m 1) = 0 := by
  have h := coeff_polOf φ d m hm
  rw [hP, coeff_zero] at h
  have hne : (Nat.multinomial Finset.univ m : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.multinomial_pos _ _).ne'
  rcases mul_eq_zero.mp h.symm with h1 | h1
  · exact absurd h1 hne
  · exact h1

theorem homog_kill (φ : Module.Dual ℝ (MvPolynomial σ ℝ)) (d : ℕ) (hP : polOf φ d = 0)
    (Q : MvPolynomial σ ℝ) (hQ : Q.IsHomogeneous d) : φ Q = 0 := by
  rw [Q.as_sum, map_sum]
  refine Finset.sum_eq_zero fun m hm => ?_
  have hdeg : ∑ x, m x = d := by
    have := hQ (mem_support_iff.mp hm)
    simpa [Finsupp.weight_apply, Finsupp.sum_fintype] using this
  have : monomial m (coeff m Q) = coeff m Q • monomial m (1 : ℝ) := by
    rw [smul_monomial, smul_eq_mul, mul_one]
  rw [this, map_smul, monomial_kill φ d hP m hdeg, smul_zero]

theorem span_pow_linRoot : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (N d : ℕ) (Q : MvPolynomial (ι × Fin N) ℝ),
    Q.IsHomogeneous d →
    Q ∈ Submodule.span ℝ ((fun u => Formalism.DegreeFormula.linRoot u ^ d) '' {u : ι → Fin N → ℝ | ∀ τ, StrictAnti (u τ)}) := by
  intro ι _ _ N d Q hQ
  by_contra hnot
  obtain ⟨φ, hφQ, hφ⟩ := Submodule.exists_dual_map_eq_bot_of_notMem hnot inferInstance
  have hkill : ∀ u : ι → Fin N → ℝ, (∀ τ, StrictAnti (u τ)) →
      φ ((∑ x : ι × Fin N, C (u x.1 x.2) * X x) ^ d) = 0 := by
    intro u hu
    have hmem : Formalism.DegreeFormula.linRoot u ^ d ∈ Submodule.span ℝ ((fun u => Formalism.DegreeFormula.linRoot u ^ d) ''
        {u : ι → Fin N → ℝ | ∀ τ, StrictAnti (u τ)}) := Submodule.subset_span ⟨u, hu, rfl⟩
    have h0 : φ (Formalism.DegreeFormula.linRoot u ^ d) = 0 := by
      have := Submodule.mem_map_of_mem (f := φ) hmem
      rw [hφ] at this
      simpa using this
    rw [Formalism.DegreeFormula.linRoot, neg_pow] at h0
    rcases neg_one_pow_eq_or (MvPolynomial (ι × Fin N) ℝ) d with h | h <;> rw [h] at h0
    · simpa using h0
    · simpa using h0
  have hP : polOf φ d = 0 := by
    refine eq_zero_of_eval_zero_at_prod_finset (polOf φ d)
      (fun x => (Finset.range (d + 1)).image (fun k : ℕ => (k : ℝ) - (x.2 : ℝ) * (d + 1))) ?_ ?_
    · intro x
      rw [Finset.card_image_of_injective]
      · simpa using Nat.lt_succ_of_le (degreeOf_polOf_le φ d x)
      · intro a b hab
        simpa using hab
    · intro v hv
      rw [eval_polOf]
      have := hkill (fun τ i => v (τ, i)) ?_
      · simpa using this
      intro τ i j hij
      obtain ⟨a, ha, hva⟩ := Finset.mem_image.mp (hv (τ, i))
      obtain ⟨b, hb, hvb⟩ := Finset.mem_image.mp (hv (τ, j))
      simp only [Finset.mem_range] at ha hb
      have hij' : (i : ℝ) + 1 ≤ (j : ℝ) := by
        have : (i : ℕ) + 1 ≤ (j : ℕ) := hij
        exact_mod_cast this
      have hb' : (b : ℝ) ≤ d := by exact_mod_cast Nat.lt_succ_iff.mp hb
      have ha' : (0 : ℝ) ≤ a := Nat.cast_nonneg a
      show v (τ, j) < v (τ, i)
      rw [← hva, ← hvb]
      simp only
      nlinarith
  exact hφQ (homog_kill φ d hP Q hQ)

end PowLinSpan
end GlobalTheory
