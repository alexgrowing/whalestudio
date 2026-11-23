import Formalism.DegreeFormula.FlagDegFormula

open MvPolynomial

namespace Formalism.DegreeFormula.PermutationPointDegree
open Formalism.DegreeFormula

theorem permExp_inj {ι : Type} [Fintype ι] {N : ℕ} (σ ρ : ι → Equiv.Perm (Fin N))
    (h : permExp σ = permExp ρ) : σ = ρ := by
  funext τ
  ext i
  have := DFunLike.congr_fun h (τ, i)
  simp only [permExp, Finsupp.equivFunOnFinite_symm_apply_apply] at this
  have h1 := (σ τ i).isLt
  have h2 := (ρ τ i).isLt
  omega

theorem sum_delta (N : ℕ) : ∑ i : Fin N, (N - 1 - (i : ℕ)) = N * (N - 1) / 2 := by
  rw [← Finset.sum_range_id]
  rw [← Fin.sum_univ_eq_sum_range]
  refine Fintype.sum_equiv Fin.revPerm _ _ ?_
  intro i
  simp [Fin.val_rev]
  omega

theorem prod_negX {ι : Type} [Fintype ι] {N : ℕ} (e : ι × Fin N → ℕ) :
    (∏ x : ι × Fin N, (-X x : MvPolynomial (ι × Fin N) ℝ) ^ (e x)) =
      C ((-1 : ℝ) ^ (∑ x, e x)) * monomial (Finsupp.equivFunOnFinite.symm e) 1 := by
  rw [Finset.prod_congr rfl (fun x _ => neg_pow (X x : MvPolynomial (ι × Fin N) ℝ) (e x)),
    Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, monomial_eq,
    Finsupp.prod_fintype _ _ (by intro i; simp)]
  simp only [Finsupp.equivFunOnFinite_symm_apply_apply, map_pow, map_neg, map_one, one_mul]

theorem degFlPoint : DegFlPoint := by
  intro ι _ _ N
  rw [prod_negX]
  unfold degFl
  rw [Finset.sum_eq_single (fun _ => 1)]
  · have hs : ∑ x : ι × Fin N, (N - 1 - (x.2 : ℕ)) = dimFl ι N := by
      rw [Fintype.sum_prod_type]
      simp [sum_delta, dimFl]
    have he : permExp (fun _ : ι => (1 : Equiv.Perm (Fin N))) =
        Finsupp.equivFunOnFinite.symm (fun x : ι × Fin N => N - 1 - (x.2 : ℕ)) := by
      ext x; simp [permExp]
    rw [he, coeff_C_mul, coeff_monomial, if_pos rfl, hs]
    simp [← pow_add, ← two_mul, pow_mul]
  · intro σ _ hσ
    have he : permExp (fun _ : ι => (1 : Equiv.Perm (Fin N))) =
        Finsupp.equivFunOnFinite.symm (fun x : ι × Fin N => N - 1 - (x.2 : ℕ)) := by
      ext x; simp [permExp]
    rw [coeff_C_mul, coeff_monomial, ← he, if_neg]
    · simp
    · intro h; exact hσ (permExp_inj _ _ h).symm
  · simp

end Formalism.DegreeFormula.PermutationPointDegree

namespace Formalism.DegreeFormula

theorem degreePoint : DegFlPoint := Formalism.DegreeFormula.PermutationPointDegree.degFlPoint

end Formalism.DegreeFormula
