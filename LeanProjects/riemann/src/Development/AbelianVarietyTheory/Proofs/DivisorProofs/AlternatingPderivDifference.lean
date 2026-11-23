import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsFlagBundleRankOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OddHarmZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RenameSwapOfEqualPartialsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MonomialPderivDifferencePrimitiveExistsStatement
open MvPolynomial GlobalTheory.CovTest GlobalTheory.ArInt GlobalTheory.BlockPoint

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.AltPrim

theorem alt_monomial_eq_zero' {n : ℕ} (ψ : MvPolynomial (Fin n) ℝ →ₗ[ℝ] ℝ)
    (hψ : ∀ (σ : Equiv.Perm (Fin n)) (P : MvPolynomial (Fin n) ℝ),
      ψ (MvPolynomial.rename σ P) = ((Equiv.Perm.sign σ : ℤ) : ℝ) * ψ P)
    (α : Fin n →₀ ℕ) (c : ℝ) {i j : Fin n} (hij : i ≠ j) (he : α i = α j) :
    ψ (monomial α c) = 0 := by
  have h1 : MvPolynomial.rename (Equiv.swap i j) (monomial α c) = monomial α c := by
    have hα : Finsupp.mapDomain (Equiv.swap i j) α = α := by
      ext k
      rw [Finsupp.mapDomain_equiv_apply, Equiv.symm_swap]
      rcases eq_or_ne k i with rfl | hki
      · rw [Equiv.swap_apply_left, he]
      rcases eq_or_ne k j with rfl | hkj
      · rw [Equiv.swap_apply_right, he]
      · rw [Equiv.swap_apply_of_ne_of_ne hki hkj]
    rw [rename_monomial, hα]
  have h2 := hψ (Equiv.swap i j) (monomial α c)
  rw [h1, Equiv.Perm.sign_swap hij] at h2
  push_cast at h2
  linarith

theorem prod_neg_X_pow_eq_monomial : ∀ (n : ℕ) (τ : Equiv.Perm (Fin (n + 1))), (∏ j : Fin (n + 1), (-X (τ j) : MvPolynomial (Fin (n + 1)) ℝ) ^ (n - (j : ℕ))) = monomial (Finsupp.equivFunOnFinite.symm (fun k : Fin (n + 1) => n - ((τ.symm k : Fin (n + 1)) : ℕ))) ((-1 : ℝ) ^ (∑ j : Fin (n + 1), (n - (j : ℕ)))) := by
  intro n τ
  have hexp : (∑ j : Fin (n + 1), Finsupp.single (τ j) (n - (j : ℕ))) =
      Finsupp.equivFunOnFinite.symm (fun k : Fin (n + 1) => n - ((τ.symm k : Fin (n + 1)) : ℕ)) := by
    ext k
    rw [Finsupp.finset_sum_apply, Finsupp.coe_equivFunOnFinite_symm]
    simp only [Finsupp.single_apply]
    rw [Finset.sum_eq_single (τ.symm k)]
    · simp
    · intro b _ hb
      rw [if_neg]
      intro h; apply hb; rw [← h, Equiv.symm_apply_apply]
    · simp
  have hj : ∀ j : Fin (n + 1), (-X (τ j) : MvPolynomial (Fin (n + 1)) ℝ) ^ (n - (j : ℕ)) =
      C ((-1 : ℝ) ^ (n - (j : ℕ))) * monomial (Finsupp.single (τ j) (n - (j : ℕ))) 1 := by
    intro j
    rw [neg_pow, X_pow_eq_monomial, C_pow, C_neg, C_1]
  rw [Finset.prod_congr rfl (fun j _ => hj j), Finset.prod_mul_distrib, ← map_prod, Finset.prod_pow_eq_pow_sum,
    ← monomial_sum_one, hexp, C_mul_monomial, mul_one]

theorem expo_apply (n : ℕ) (τ : Equiv.Perm (Fin (n + 1))) (k : Fin (n + 1)) :
    (Finsupp.equivFunOnFinite.symm (fun k : Fin (n + 1) => n - ((τ.symm k : Fin (n + 1)) : ℕ))) k = n - (τ.symm k : ℕ) := rfl

theorem alt_X_mul_eq_zero (n : ℕ) (ψ : MvPolynomial (Fin (n + 1)) ℝ →ₗ[ℝ] ℝ)
    (hψ : ∀ (σ : Equiv.Perm (Fin (n + 1))) (P : MvPolynomial (Fin (n + 1)) ℝ),
      ψ (MvPolynomial.rename σ P) = ((Equiv.Perm.sign σ : ℤ) : ℝ) * ψ P)
    (τ : Equiv.Perm (Fin (n + 1))) (k : Fin (n + 1)) (hk : k ≠ τ 0) :
    ψ (X k * ∏ j : Fin (n + 1), (-X (τ j)) ^ (n - (j : ℕ))) = 0 := by
  rw [prod_neg_X_pow_eq_monomial, X, monomial_mul, one_mul]
  have hpos : (τ.symm k : ℕ) ≠ 0 := by
    intro h; apply hk
    have : τ.symm k = 0 := Fin.ext (by simpa using h)
    rw [← this, Equiv.apply_symm_apply]
  have hlt : (τ.symm k : ℕ) - 1 < n + 1 := by omega
  set l : Fin (n + 1) := τ ⟨(τ.symm k : ℕ) - 1, hlt⟩ with hl
  have hlk : k ≠ l := by
    intro h
    have := congrArg (fun x => (τ.symm x : ℕ)) h
    simp [hl] at this
    omega
  refine alt_monomial_eq_zero' ψ hψ _ _ hlk ?_
  have e1 : (τ.symm l : ℕ) = τ.symm k - 1 := by simp [hl]
  have e2 : (Finsupp.single k 1 : Fin (n + 1) →₀ ℕ) l = 0 := by
    rw [Finsupp.single_apply, if_neg hlk]
  rw [Finsupp.add_apply, Finsupp.add_apply, Finsupp.single_eq_same, e2, expo_apply, expo_apply, e1]
  have := (τ.symm k).isLt
  omega

theorem exists_antideriv (n : ℕ) (ψ : MvPolynomial (Fin (n + 1)) ℝ →ₗ[ℝ] ℝ)
    (hψ : ∀ (σ : Equiv.Perm (Fin (n + 1))) (P : MvPolynomial (Fin (n + 1)) ℝ),
      ψ (MvPolynomial.rename σ P) = ((Equiv.Perm.sign σ : ℤ) : ℝ) * ψ P)
    (i i' : Fin (n + 1)) (hne : i ≠ i') (τ : Equiv.Perm (Fin (n + 1))) (hτ : (τ.symm i : ℕ) < τ.symm i') :
    ∃ J₁ : MvPolynomial (Fin (n + 1)) ℝ,
      pderiv i' J₁ - pderiv i J₁ = ∏ j : Fin (n + 1), (-X (τ j)) ^ (n - (j : ℕ)) ∧
      ψ J₁ = -(1 / ((n : ℝ) - (τ.symm i : ℕ) + 1)) * ψ (X i * ∏ j : Fin (n + 1), (-X (τ j)) ^ (n - (j : ℕ))) := by
  obtain ⟨J₁, R, hD, hJ, hR⟩ := GlobalTheory.T.monomial_pderiv_difference_primitive_exists n i i' hne
    (Finsupp.equivFunOnFinite.symm (fun k : Fin (n + 1) => n - ((τ.symm k : Fin (n + 1)) : ℕ)))
    ((-1 : ℝ) ^ (∑ j : Fin (n + 1), (n - (j : ℕ))))
  refine ⟨J₁, by rw [hD, prod_neg_X_pow_eq_monomial], ?_⟩
  have hR0 : ψ R = 0 := by
    rw [R.as_sum, map_sum]
    refine Finset.sum_eq_zero fun β hβ => ?_
    obtain ⟨h1, h2⟩ := hR β hβ
    rw [expo_apply] at h1
    have hi'le := (τ.symm i').isLt
    set e := β i' with he
    have hle : n - e < n + 1 := by omega
    set j : Fin (n + 1) := τ ⟨n - e, hle⟩ with hj
    have hje : (τ.symm j : ℕ) = n - e := by simp [hj]
    have hji' : j ≠ i' := by
      intro h; rw [h] at hje; omega
    have hji : j ≠ i := by
      intro h; rw [h] at hje; omega
    refine alt_monomial_eq_zero' ψ hψ β _ hji' ?_
    rw [h2 j hji hji', expo_apply, hje]
    omega
  rw [hJ, map_add, hR0, add_zero, map_smul, prod_neg_X_pow_eq_monomial, expo_apply, smul_eq_mul]
  have := (τ.symm i).isLt
  congr 3
  push_cast [Nat.cast_sub (by omega : (τ.symm i : ℕ) ≤ n)]
  ring

theorem alt_eq_zero_of_pderiv_eq {n : ℕ} (ψ : MvPolynomial (Fin (n + 1)) ℝ →ₗ[ℝ] ℝ)
    (hψ : ∀ (σ : Equiv.Perm (Fin (n + 1))) (P : MvPolynomial (Fin (n + 1)) ℝ),
      ψ (MvPolynomial.rename σ P) = ((Equiv.Perm.sign σ : ℤ) : ℝ) * ψ P)
    {i i' : Fin (n + 1)} (hne : i ≠ i') (K : MvPolynomial (Fin (n + 1)) ℝ) (hK : pderiv i' K = pderiv i K) :
    ψ K = 0 := by
  have h2 := hψ (Equiv.swap i i') K
  rw [GlobalTheory.T.rename_swap_of_equal_partials n i i' K hK, Equiv.Perm.sign_swap hne] at h2
  push_cast at h2
  linarith

theorem rename_swap_prod (n : ℕ) (i i' : Fin (n + 1)) (τ : Equiv.Perm (Fin (n + 1))) :
    rename (Equiv.swap i i') (∏ j : Fin (n + 1), (-X (τ j) : MvPolynomial (Fin (n + 1)) ℝ) ^ (n - (j : ℕ))) =
      ∏ j : Fin (n + 1), (-X (Equiv.swap i i' (τ j))) ^ (n - (j : ℕ)) := by
  simp [map_prod]

theorem alt_sum_mul (n : ℕ) (ψ : MvPolynomial (Fin (n + 1)) ℝ →ₗ[ℝ] ℝ)
    (hψ : ∀ (σ : Equiv.Perm (Fin (n + 1))) (P : MvPolynomial (Fin (n + 1)) ℝ),
      ψ (MvPolynomial.rename σ P) = ((Equiv.Perm.sign σ : ℤ) : ℝ) * ψ P)
    (τ : Equiv.Perm (Fin (n + 1))) :
    ψ (X (τ 0) * ∏ j : Fin (n + 1), (-X (τ j)) ^ (n - (j : ℕ))) =
      ((Equiv.Perm.sign τ : ℤ) : ℝ) * ψ ((∑ j : Fin (n + 1), X j) * ∏ j : Fin (n + 1), (-X j) ^ (n - (j : ℕ))) := by
  have h1 : rename τ ((∑ j : Fin (n + 1), X j) * ∏ j : Fin (n + 1), (-X j : MvPolynomial (Fin (n + 1)) ℝ) ^ (n - (j : ℕ)))
      = (∑ j : Fin (n + 1), X j) * ∏ j : Fin (n + 1), (-X (τ j)) ^ (n - (j : ℕ)) := by
    simp only [map_mul, map_sum, map_prod, map_pow, map_neg, rename_X]
    congr 1
    exact Equiv.sum_comp τ (fun j => (X j : MvPolynomial (Fin (n + 1)) ℝ))
  rw [← hψ, h1, Finset.sum_mul, map_sum, Finset.sum_eq_single (τ 0)]
  · intro k _ hk
    exact alt_X_mul_eq_zero n ψ hψ τ k hk
  · simp

end GlobalTheory.AltPrim

namespace GlobalTheory.AltPrim

theorem alt_eq_of_pderiv_sub (n : ℕ) (ψ : MvPolynomial (Fin (n + 1)) ℝ →ₗ[ℝ] ℝ)
    (hψ : ∀ (σ : Equiv.Perm (Fin (n + 1))) (P : MvPolynomial (Fin (n + 1)) ℝ),
      ψ (MvPolynomial.rename σ P) = ((Equiv.Perm.sign σ : ℤ) : ℝ) * ψ P)
    (i i' : Fin (n + 1)) (hne : i ≠ i') (τ : Equiv.Perm (Fin (n + 1))) (hτ : (τ.symm i : ℕ) < τ.symm i')
    (J : MvPolynomial (Fin (n + 1)) ℝ)
    (hJ : pderiv i' J - pderiv i J = (∏ j : Fin (n + 1), (-X (τ j)) ^ (n - (j : ℕ))) +
      ∏ j : Fin (n + 1), (-X (Equiv.swap i i' (τ j))) ^ (n - (j : ℕ))) :
    ψ J = -(2 / ((n : ℝ) - (τ.symm i : ℕ) + 1)) * ψ (X i * ∏ j : Fin (n + 1), (-X (τ j)) ^ (n - (j : ℕ))) := by
  obtain ⟨J₁, hD, hv⟩ := exists_antideriv n ψ hψ i i' hne τ hτ
  have hs := rename_swap_prod n i i' τ
  have hinj : Function.Injective (Equiv.swap i i') := (Equiv.swap i i').injective
  have a1 : pderiv i' (rename (Equiv.swap i i') J₁) = rename (Equiv.swap i i') (pderiv i J₁) := by
    have := pderiv_rename hinj i J₁
    rwa [Equiv.swap_apply_left] at this
  have a2 : pderiv i (rename (Equiv.swap i i') J₁) = rename (Equiv.swap i i') (pderiv i' J₁) := by
    have := pderiv_rename hinj i' J₁
    rwa [Equiv.swap_apply_right] at this
  have hD' : pderiv i' (rename (Equiv.swap i i') J₁) - pderiv i (rename (Equiv.swap i i') J₁) =
      - rename (Equiv.swap i i') (∏ j : Fin (n + 1), (-X (τ j)) ^ (n - (j : ℕ))) := by
    rw [a1, a2, ← hD, map_sub]; ring
  have hK := alt_eq_zero_of_pderiv_eq ψ hψ hne (J - (J₁ - rename (Equiv.swap i i') J₁)) (by
    rw [← sub_eq_zero]
    simp only [map_sub]
    linear_combination hJ - hD + hD' - hs)
  have hs1 := hψ (Equiv.swap i i') J₁
  rw [Equiv.Perm.sign_swap hne] at hs1
  push_cast at hs1
  rw [map_sub, map_sub] at hK
  have : ψ J = 2 * ψ J₁ := by linarith
  rw [this, hv]; ring

theorem alt_value : ∀ (n : ℕ) (ψ : MvPolynomial (Fin (n + 1)) ℝ →ₗ[ℝ] ℝ), (∀ (σ : Equiv.Perm (Fin (n + 1))) (P : MvPolynomial (Fin (n + 1)) ℝ), ψ (MvPolynomial.rename σ P) = ((Equiv.Perm.sign σ : ℤ) : ℝ) * ψ P) → ∀ (σ : Equiv.Perm (Fin (n + 1))) (i i' : Fin (n + 1)), (i' : ℕ) = i + 1 → ∀ J : MvPolynomial (Fin (n + 1)) ℝ, J.IsHomogeneous (∑ j : Fin (n + 1), (j : ℕ) + 1) → MvPolynomial.pderiv i' J - MvPolynomial.pderiv i J = (∏ j : Fin (n + 1), (-MvPolynomial.X (σ j)) ^ (n - (j : ℕ))) + (∏ j : Fin (n + 1), (-MvPolynomial.X (Equiv.swap i i' (σ j))) ^ (n - (j : ℕ))) → ψ J = ((Equiv.Perm.sign σ : ℤ) : ℝ) * (2 / ((n : ℝ) + 1)) * (((σ 0 : ℕ) : ℝ) - ((Equiv.swap i i' (σ 0) : ℕ) : ℝ)) * ψ ((∑ j : Fin (n + 1), MvPolynomial.X j) * ∏ j : Fin (n + 1), (-MvPolynomial.X j) ^ (n - (j : ℕ))) := by
  intro n ψ hψ σ i i' hi J _hJ hD
  have hne : i ≠ i' := by
    intro h; rw [h] at hi; omega
  have hii : ((i' : ℕ) : ℝ) = (i : ℕ) + 1 := by rw [hi]; push_cast; ring

  have hD2 : pderiv i' J - pderiv i J =
      (∏ j : Fin (n + 1), (-X ((Equiv.swap i i' * σ) j)) ^ (n - (j : ℕ))) +
      ∏ j : Fin (n + 1), (-X (Equiv.swap i i' ((Equiv.swap i i' * σ) j))) ^ (n - (j : ℕ)) := by
    simp only [Equiv.Perm.mul_apply, Equiv.swap_apply_self]
    rw [hD]; exact add_comm _ _
  have hsy1 : (Equiv.swap i i' * σ).symm i = σ.symm i' := by
    rw [Equiv.symm_apply_eq]; simp [Equiv.Perm.mul_apply]
  have hsy2 : (Equiv.swap i i' * σ).symm i' = σ.symm i := by
    rw [Equiv.symm_apply_eq]; simp [Equiv.Perm.mul_apply]
  have hsign : ((Equiv.Perm.sign (Equiv.swap i i' * σ) : ℤ) : ℝ) = -((Equiv.Perm.sign σ : ℤ) : ℝ) := by
    rw [Equiv.Perm.sign_mul, Equiv.Perm.sign_swap hne]; push_cast; ring
  by_cases h0 : σ 0 = i
  · have e1 : σ.symm i = 0 := by rw [← h0]; simp
    have e2 : (σ.symm i' : ℕ) ≠ 0 := by
      intro h
      apply hne
      have : σ.symm i' = 0 := Fin.ext (by simpa using h)
      rw [← h0, ← this, Equiv.apply_symm_apply]
    have hτ : (σ.symm i : ℕ) < σ.symm i' := by rw [e1, Fin.val_zero]; exact Nat.pos_of_ne_zero e2
    have key := alt_eq_of_pderiv_sub n ψ hψ i i' hne σ hτ J hD
    have hsum := alt_sum_mul n ψ hψ σ
    rw [h0] at hsum
    rw [key, hsum, h0, Equiv.swap_apply_left, e1, hii]
    simp only [Fin.val_zero, Nat.cast_zero]
    ring
  by_cases h0' : σ 0 = i'
  · have e1 : (Equiv.swap i i' * σ).symm i = 0 := by rw [hsy1, ← h0']; simp
    have e2 : ((Equiv.swap i i' * σ).symm i' : ℕ) ≠ 0 := by
      rw [hsy2]
      intro h
      apply hne
      have : σ.symm i = 0 := Fin.ext (by simpa using h)
      rw [← h0', ← this, Equiv.apply_symm_apply]
    have hτ : ((Equiv.swap i i' * σ).symm i : ℕ) < (Equiv.swap i i' * σ).symm i' := by rw [e1, Fin.val_zero]; exact Nat.pos_of_ne_zero e2
    have key := alt_eq_of_pderiv_sub n ψ hψ i i' hne _ hτ J hD2
    have hsum := alt_sum_mul n ψ hψ (Equiv.swap i i' * σ)
    have ht0 : (Equiv.swap i i' * σ) 0 = i := by simp [Equiv.Perm.mul_apply, h0']
    rw [ht0, hsign] at hsum
    rw [key, hsum, h0', Equiv.swap_apply_right, e1, hii]
    simp only [Fin.val_zero, Nat.cast_zero]
    ring
  · have hfix : Equiv.swap i i' (σ 0) = σ 0 := Equiv.swap_apply_of_ne_of_ne h0 h0'
    rw [hfix, sub_self, mul_zero, zero_mul]
    have hdist : (σ.symm i : ℕ) ≠ σ.symm i' := by
      intro h; apply hne; exact σ.symm.injective (Fin.ext h)
    rcases lt_or_gt_of_ne hdist with hlt | hgt
    · rw [alt_eq_of_pderiv_sub n ψ hψ i i' hne σ hlt J hD, alt_X_mul_eq_zero n ψ hψ σ i (Ne.symm h0), mul_zero]
    · have hτ : ((Equiv.swap i i' * σ).symm i : ℕ) < (Equiv.swap i i' * σ).symm i' := by rw [hsy1, hsy2]; exact hgt
      have ht0 : (Equiv.swap i i' * σ) 0 ≠ i := by simp [Equiv.Perm.mul_apply, hfix, h0]
      rw [alt_eq_of_pderiv_sub n ψ hψ i i' hne _ hτ J hD2, alt_X_mul_eq_zero n ψ hψ _ i (Ne.symm ht0), mul_zero]

end GlobalTheory.AltPrim
