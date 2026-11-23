import Formalism.SharpRestriction.GrowthBounds.RootWeights.GlOperatorPreservesMultidegree

noncomputable section

open MvPolynomial Finset

namespace Formalism.MainNotions.G.GLWeightTheory

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees

variable {K : Type} [Field K] {ι : Type} [Fintype ι] {n : ℕ}

theorem monomial_shift_cancel {σ : Type} (m : σ →₀ ℕ) (v : σ) (c : K) :
    (monomial (m - Finsupp.single v 1 + Finsupp.single v 1) (c * (m v : K)) : MvPolynomial σ K) =
      monomial m (c * (m v : K)) := by
  by_cases h : m v = 0
  · simp [h]
  · rw [tsub_add_cancel_of_le]
    rw [Finsupp.single_le_iff]
    omega

theorem diagonal_derivation_monomial (LL : Letters ι) (S : Set ι) (a : Fin n) (m : ι × Fin n →₀ ℕ) (c : K) :
    glDerivation K LL S a a (monomial m c) = monomial m (((wtS LL S m a : ℤ) : K) * c) := by
  rw [gl_derivation_monomial]
  simp only [monomial_shift_cancel]
  unfold wtS
  rw [Int.cast_sum, Finset.sum_mul, map_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  split_ifs <;> simp [mul_comm]

theorem diagonal_derivation_coeff (LL : Letters ι) (S : Set ι) (a : Fin n) (F : MvPolynomial (ι × Fin n) K)
    (m : ι × Fin n →₀ ℕ) :
    coeff m (glDerivation K LL S a a F) = ((wtS LL S m a : ℤ) : K) * coeff m F := by
  classical
  induction F using MvPolynomial.induction_on' with
  | monomial u b =>
    rw [diagonal_derivation_monomial, coeff_monomial, coeff_monomial]
    split_ifs with h
    · subst h
      rfl
    · simp
  | add p q hp hq =>
    rw [map_add, coeff_add, hp, hq, coeff_add, mul_add]

theorem polynomial_mem_weightSpace_iff (LL : Letters ι) (S : Set ι) (mu : Fin n → ℤ) (F : MvPolynomial (ι × Fin n) K) :
    F ∈ weightSp (glOps K n LL S) mu ↔ ∀ a, glDerivation K LL S a a F = ((mu a : ℤ) : K) • F := by
  simp only [weightSp, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
    LinearMap.smul_apply, sub_eq_zero, gl_operator_apply_derivation]
  rfl

theorem weight_vector_monomial_weight [CharZero K] (LL : Letters ι) (S : Set ι) (mu : Fin n → ℤ) (F : MvPolynomial (ι × Fin n) K)
    (hF : F ∈ weightSp (glOps K n LL S) mu) (m : ι × Fin n →₀ ℕ) (hm : m ∈ F.support) : wtS LL S m = mu := by
  funext a
  have h := congrArg (coeff m) ((polynomial_mem_weightSpace_iff LL S mu F).1 hF a)
  rw [diagonal_derivation_coeff, coeff_smul, smul_eq_mul] at h
  have hc : coeff m F ≠ 0 := mem_support_iff.1 hm
  have h2 := mul_right_cancel₀ hc h
  exact_mod_cast h2

theorem monomial_mem_weightSpace (LL : Letters ι) (S : Set ι) (m : ι × Fin n →₀ ℕ) (c : K) :
    monomial m c ∈ weightSp (glOps K n LL S) (wtS LL S m) := by
  rw [polynomial_mem_weightSpace_iff]
  intro a
  rw [diagonal_derivation_monomial, smul_monomial, smul_eq_mul]

theorem polynomial_isGLRep (LL : Letters ι) (S : Set ι) : IsGLRep (glOps K n LL S) := by
  classical
  refine ⟨polynomial_gl_commutation LL S, ?_, ?_⟩
  · intro x
    haveI : ∀ m : x.support, FiniteDimensional K (Pol K n (fun i => multideg (m : ι × Fin n →₀ ℕ) i)) :=
      fun m => homogeneous_multidegree_findim _
    refine ⟨⨆ m : x.support, Pol K n (fun i => multideg (m : ι × Fin n →₀ ℕ) i), inferInstance, ?_, ?_⟩
    · have key : ∑ m ∈ x.support, monomial m (coeff m x) ∈
          ⨆ m : x.support, Pol K n (fun i => multideg (m : ι × Fin n →₀ ℕ) i) := by
        apply Submodule.sum_mem
        intro m hm
        apply Submodule.mem_iSup_of_mem (⟨m, hm⟩ : x.support)
        rw [Pol, mem_restrictSupport_iff]
        intro m' hm'
        have h1 := support_monomial_subset (Finset.mem_coe.1 hm')
        rw [Finset.mem_singleton] at h1
        subst h1
        intro i
        rfl
      convert key using 1
      exact x.as_sum
    · intro a b y hy
      refine Submodule.iSup_induction _ (motive := fun y => glOps K n LL S a b y ∈
        ⨆ m : x.support, Pol K n (fun i => multideg (m : ι × Fin n →₀ ℕ) i)) hy ?_ ?_ ?_
      · intro m z hz
        exact Submodule.mem_iSup_of_mem m (gl_operator_preserves_multidegree LL S _ a b z hz)
      · simp
      · intro z w hz hw
        rw [map_add]
        exact Submodule.add_mem _ hz hw
  · rw [eq_top_iff]
    intro F _
    have key : ∑ m ∈ F.support, monomial m (coeff m F) ∈ ⨆ mu : Fin n → ℤ, weightSp (glOps K n LL S) mu := by
      apply Submodule.sum_mem
      intro m _
      exact Submodule.mem_iSup_of_mem (wtS LL S m) (monomial_mem_weightSpace LL S m _)
    convert key using 1
    exact F.as_sum

end Formalism.MainNotions.G.GLWeightTheory
