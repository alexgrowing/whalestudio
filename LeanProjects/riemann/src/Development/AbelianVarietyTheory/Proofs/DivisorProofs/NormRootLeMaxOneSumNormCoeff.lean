import Mathlib

namespace GlobalTheory

theorem norm_eval₂Hom_le_sum_norm_coeff_of_norm_le_one {A K : Type} [CommRing A] [NormedField K]
    (ψ : A →+* K) {d : ℕ} (ζ : Fin d → K) (hζ : ∀ j, ‖ζ j‖ ≤ 1) (q : MvPolynomial (Fin d) A) :
    ‖MvPolynomial.eval₂Hom ψ ζ q‖ ≤ ∑ s ∈ q.support, ‖ψ (q.coeff s)‖ := by
  rw [MvPolynomial.coe_eval₂Hom, MvPolynomial.eval₂_eq]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun s _ => ?_)
  rw [norm_mul]
  refine mul_le_of_le_one_right (norm_nonneg _) ?_
  rw [norm_prod]
  refine Finset.prod_le_one (fun _ _ => norm_nonneg _) fun i _ => ?_
  rw [norm_pow]
  exact pow_le_one₀ (norm_nonneg _) (hζ i)

theorem norm_root_le_max_one_sum_norm_coeff :
    ∀ {A K : Type} [CommRing A] [NormedField K] (ψ : A →+* K) {d : ℕ} (ζ : Fin d → K), (∀ j, ‖ζ j‖ ≤ 1) →
    ∀ (p : Polynomial (MvPolynomial (Fin d) A)), p.Monic → ∀ (α : K),
      p.eval₂ (MvPolynomial.eval₂Hom ψ ζ) α = 0 →
      ‖α‖ ≤ max 1 (∑ l ∈ Finset.range p.natDegree, ∑ s ∈ (p.coeff l).support, ‖ψ ((p.coeff l).coeff s)‖) := by
  intro A K _ _ ψ d ζ hζ p hp α hα
  by_cases h1 : ‖α‖ ≤ 1
  · exact le_max_of_le_left h1
  have h1 : 1 < ‖α‖ := not_le.mp h1
  refine le_max_of_le_right ?_
  rw [Polynomial.eval₂_eq_sum_range, Finset.sum_range_succ, hp.coeff_natDegree, map_one,
    one_mul] at hα
  set n := p.natDegree with hn
  set S := ∑ l ∈ Finset.range n, ∑ s ∈ (p.coeff l).support, ‖ψ ((p.coeff l).coeff s)‖ with hS
  have hpos : 0 < ‖α‖ := zero_lt_one.trans h1
  have e : α ^ n = -∑ l ∈ Finset.range n, MvPolynomial.eval₂Hom ψ ζ (p.coeff l) * α ^ l :=
    eq_neg_of_add_eq_zero_right hα
  have key : ‖α‖ * ‖α‖ ^ n ≤ S * ‖α‖ ^ n := by
    calc ‖α‖ * ‖α‖ ^ n = ‖α‖ * ‖α ^ n‖ := by rw [norm_pow]
      _ ≤ ‖α‖ * ∑ l ∈ Finset.range n, ‖MvPolynomial.eval₂Hom ψ ζ (p.coeff l) * α ^ l‖ := by
          refine mul_le_mul_of_nonneg_left ?_ hpos.le
          rw [e, norm_neg]
          exact norm_sum_le _ _
      _ ≤ S * ‖α‖ ^ n := by
          rw [hS, Finset.mul_sum, Finset.sum_mul]
          refine Finset.sum_le_sum fun l hl => ?_
          have hl' : l + 1 ≤ n := Finset.mem_range.mp hl
          have h2 := norm_eval₂Hom_le_sum_norm_coeff_of_norm_le_one ψ ζ hζ (p.coeff l)
          have h3 : ‖α‖ ^ (l + 1) ≤ ‖α‖ ^ n := pow_le_pow_right₀ h1.le hl'
          rw [norm_mul, norm_pow]
          calc ‖α‖ * (‖MvPolynomial.eval₂Hom ψ ζ (p.coeff l)‖ * ‖α‖ ^ l)
              = ‖MvPolynomial.eval₂Hom ψ ζ (p.coeff l)‖ * ‖α‖ ^ (l + 1) := by ring
            _ ≤ _ := mul_le_mul h2 h3 (by positivity) ((norm_nonneg _).trans h2)
  exact le_of_mul_le_mul_right key (pow_pos hpos n)

end GlobalTheory
