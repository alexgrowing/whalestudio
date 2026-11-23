import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.AmpleOnAbelianBase
open GlobalTheory.ShFam.Pad

namespace GlobalTheory.NumLRename

theorem numL_monomial {A : Type} (num : Multiset A → ℝ) (d : ℕ) (m : A →₀ ℕ) (a : ℝ) :
    numL num d (MvPolynomial.monomial m a) = a * (if m.degree = d then num (Finsupp.toMultiset m) else 0) := by
  have h2 : MvPolynomial.monomial m a = a • MvPolynomial.basisMonomials A ℝ m := by
    simp [MvPolynomial.smul_monomial]
  rw [h2, map_smul, numL, Module.Basis.constr_basis, smul_eq_mul]

theorem prod_map_X_toMultiset {ι : Type} (m : ι →₀ ℕ) :
    ((Finsupp.toMultiset m).map MvPolynomial.X).prod = (MvPolynomial.monomial m 1 : MvPolynomial ι ℝ) := by
  classical
  rw [← MvPolynomial.prod_X_pow_eq_monomial, Finsupp.toMultiset_map, Finsupp.prod_toMultiset,
    Finsupp.prod_mapDomain_index (fun _ => pow_zero _) (fun _ _ _ => pow_add _ _ _)]
  rfl

theorem numL_rename_of_agree : ∀ {A ι : Type} (num : Multiset A → ℝ) (d : ℕ) (w : ι → A)
    (Ψ : MvPolynomial ι ℝ →ₗ[ℝ] ℝ) (c : ℝ),
    (∀ μ : Multiset ι, Multiset.card μ = d → num (μ.map w) = Ψ ((μ.map MvPolynomial.X).prod) / c) →
      ∀ P : MvPolynomial ι ℝ, P.IsHomogeneous d → numL num d (MvPolynomial.rename w P) = Ψ P / c := by
  intro A ι num d w Ψ c h P hP
  classical
  conv_lhs => rw [P.as_sum]
  conv_rhs => rw [P.as_sum]
  rw [map_sum, map_sum, map_sum, Finset.sum_div]
  refine Finset.sum_congr rfl fun m hm => ?_
  have hdeg : m.degree = d := by
    have := hP (MvPolynomial.mem_support_iff.1 hm)
    rw [Finsupp.degree_eq_weight_one]; exact this
  rw [MvPolynomial.rename_monomial, numL_monomial]
  have hdeg' : (Finsupp.mapDomain w m).degree = d := by
    rw [Finsupp.degree_mapDomain, hdeg]
  rw [if_pos hdeg', ← Finsupp.toMultiset_map]
  have hcard : Multiset.card (Finsupp.toMultiset m) = d := by
    rw [Finsupp.card_toMultiset, ← hdeg, Finsupp.degree, Finsupp.sum]; rfl
  rw [h _ hcard, prod_map_X_toMultiset]
  have : (MvPolynomial.monomial m (P.coeff m) : MvPolynomial ι ℝ) = P.coeff m • MvPolynomial.monomial m 1 := by
    simp [MvPolynomial.smul_monomial]
  rw [this, map_smul, smul_eq_mul]
  ring

end GlobalTheory.NumLRename
