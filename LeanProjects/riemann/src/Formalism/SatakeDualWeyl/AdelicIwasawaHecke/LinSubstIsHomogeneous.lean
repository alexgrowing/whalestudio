import Formalism.SatakeDualWeyl.Statement

noncomputable section

open MvPolynomial

namespace Formalism.UG.P

variable {O : Type} [CommRing O] {n : Type} [Fintype n] [DecidableEq n]

theorem linSubst_isHomogeneous (M : Matrix n n O) {k : ℕ} {P : MvPolynomial n O}
    (hP : P.IsHomogeneous k) : (linSubst O n M P).IsHomogeneous k := by
  have h := hP.aeval (fun i => ∑ j, C (M i j) * X j) (n := 1)
    (fun i => IsHomogeneous.sum _ _ _ (fun j _ => isHomogeneous_C_mul_X _ _))
  simpa [linSubst] using h

theorem nabla_subspace_stable : Formalism.UG.NablaStable := by
  intro O _ n _ _ k g P hP
  rw [nabla, mem_homogeneousSubmodule] at hP ⊢
  exact linSubst_isHomogeneous _ hP

theorem pow_sum_expand (a b : n → MvPolynomial n O) (K : ℕ) :
    (∑ j, C (a j) * map C (b j) : MvPolynomial n (MvPolynomial n O)) ^ K
      = ∑ β ∈ Finset.piAntidiag Finset.univ K,
          C ((Nat.multinomial Finset.univ β : MvPolynomial n O) * ∏ j, a j ^ β j) *
            map C (∏ j, b j ^ β j) := by
  rw [Finset.sum_pow_eq_sum_piAntidiag]
  refine Finset.sum_congr rfl (fun β _ => ?_)
  simp only [mul_pow, Finset.prod_mul_distrib, map_prod, map_pow, map_mul, map_natCast]
  ring

theorem coeff_pow_sum_expand (a b : n → MvPolynomial n O) (K : ℕ) (α : n →₀ ℕ) :
    coeff α ((∑ j, C (a j) * map C (b j) : MvPolynomial n (MvPolynomial n O)) ^ K)
      = ∑ β ∈ Finset.piAntidiag Finset.univ K,
          (Nat.multinomial Finset.univ β : MvPolynomial n O) * (∏ j, a j ^ β j) *
            C (coeff α (∏ j, b j ^ β j)) := by
  rw [pow_sum_expand, coeff_sum]
  refine Finset.sum_congr rfl (fun β _ => ?_)
  rw [coeff_C_mul, coeff_map]

theorem prod_X_pow_fun (β : n → ℕ) :
    (∏ j, X j ^ β j : MvPolynomial n O) = monomial (Finsupp.equivFunOnFinite.symm β) 1 := by
  rw [monomial_eq, C_1, one_mul, Finsupp.prod_fintype]
  · rfl
  · intro i; simp

theorem weyl_gen_eq (α : n →₀ ℕ) (K : ℕ) (hα : α.degree = K) :
    monomial α (α.multinomial : O) =
      coeff α ((∑ j, C (X j) * map C (X j) : MvPolynomial n (MvPolynomial n O)) ^ K) := by
  rw [coeff_pow_sum_expand, Finset.sum_eq_single (⇑α)]
  · have hs : Finsupp.equivFunOnFinite.symm ⇑α = α := Finsupp.equivFunOnFinite.symm_apply_apply α
    rw [prod_X_pow_fun, hs, coeff_monomial, if_pos rfl, C_1, mul_one,
      Finsupp.multinomial_of_support_subset (Finset.subset_univ _),
      ← map_natCast (C : O →+* MvPolynomial n O), C_mul_monomial, mul_one]
  · intro β _ hβ
    rw [prod_X_pow_fun, coeff_monomial, if_neg, C_0, mul_zero]
    intro h
    apply hβ
    rw [← h]
    rfl
  · intro h
    exfalso
    apply h
    rw [Finset.mem_piAntidiag]
    refine ⟨?_, fun i _ => Finset.mem_univ i⟩
    rw [← hα, Finsupp.degree_eq_sum]

theorem map_polyAct_pow (g : GL n O) (K : ℕ) :
    map (polyAct O n g).toRingHom
        ((∑ j, C (X j) * map C (X j) : MvPolynomial n (MvPolynomial n O)) ^ K)
      = (∑ i, C (X i) *
          map C (∑ j, C (((g⁻¹ : GL n O) : Matrix n n O) j i) * X j) :
            MvPolynomial n (MvPolynomial n O)) ^ K := by
  rw [map_pow]
  congr 1
  simp only [map_sum, map_mul, map_C, map_X, polyAct, linSubst, AlgHom.toRingHom_eq_coe,
    RingHom.coe_coe, aeval_X, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
  ring

theorem polyAct_weyl_gen (g : GL n O) (K : ℕ) (α : n →₀ ℕ) (hα : α.degree = K) :
    polyAct O n g (monomial α (α.multinomial : O)) ∈ weylSub O n K := by
  rw [weyl_gen_eq α K hα]
  have h1 : polyAct O n g
      (coeff α ((∑ j, C (X j) * map C (X j) : MvPolynomial n (MvPolynomial n O)) ^ K))
      = coeff α (map (polyAct O n g).toRingHom
          ((∑ j, C (X j) * map C (X j) : MvPolynomial n (MvPolynomial n O)) ^ K)) :=
    (coeff_map _ _ _).symm
  rw [h1, map_polyAct_pow, coeff_pow_sum_expand]
  refine Submodule.sum_mem _ (fun β hβ => ?_)
  have hdeg : (Finsupp.equivFunOnFinite.symm β).degree = K := by
    rw [Finsupp.degree_eq_sum]
    exact (Finset.mem_piAntidiag.mp hβ).1
  have hm : Nat.multinomial Finset.univ β = (Finsupp.equivFunOnFinite.symm β).multinomial :=
    Finsupp.multinomial_of_support_subset (s := Finset.univ)
      (d := Finsupp.equivFunOnFinite.symm β) (Finset.subset_univ _)
  rw [prod_X_pow_fun, hm]
  generalize coeff (R := O) (σ := n) α _ = c
  have he : ((Finsupp.equivFunOnFinite.symm β).multinomial : MvPolynomial n O) *
      monomial (Finsupp.equivFunOnFinite.symm β) 1 * C c
      = c • monomial (Finsupp.equivFunOnFinite.symm β)
          ((Finsupp.equivFunOnFinite.symm β).multinomial : O) := by
    rw [smul_eq_C_mul, ← map_natCast (C : O →+* MvPolynomial n O), C_mul_monomial, mul_one,
      mul_comm]
  rw [he]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, hdeg, rfl⟩)

theorem weyl_module_stable : Formalism.UG.WeylStable := by
  intro O _ n _ _ k g P hP
  have hle : weylSub O n k ≤ (weylSub O n k).comap (polyAct O n g).toLinearMap := by
    refine Submodule.span_le.mpr ?_
    rintro p ⟨α, hα, rfl⟩
    exact polyAct_weyl_gen g k α hα
  exact hle hP

end Formalism.UG.P
