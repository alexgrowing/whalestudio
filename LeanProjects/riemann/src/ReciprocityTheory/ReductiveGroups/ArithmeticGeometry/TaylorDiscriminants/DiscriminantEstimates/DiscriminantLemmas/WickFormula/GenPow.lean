import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.DiscriminantEstimates.DiscriminantLemmas.WickFormula.GenDefs

open MvPolynomial

namespace PI.WickFormula.Gen

section
variable {K I J : Type} [CommRing K] [Fintype I] [Fintype J]

theorem pderiv_comm (a b : I ⊕ J) (p : MvPolynomial (I ⊕ J) K) :
    pderiv a (pderiv b p) = pderiv b (pderiv a p) := by
  classical
  have h : ⁅(pderiv a : Derivation K (MvPolynomial (I ⊕ J) K) (MvPolynomial (I ⊕ J) K)),
      (pderiv b : Derivation K (MvPolynomial (I ⊕ J) K) (MvPolynomial (I ⊕ J) K))⁆ = 0 := by
    apply MvPolynomial.derivation_ext
    intro c
    rw [Derivation.commutator_apply, pderiv_X, pderiv_X]
    simp only [Pi.single_apply, Derivation.zero_apply]
    split_ifs <;> simp
  have h2 := congrArg (fun D : Derivation K (MvPolynomial (I ⊕ J) K) (MvPolynomial (I ⊕ J) K) =>
    D p) h
  simp only [Derivation.commutator_apply, Derivation.zero_apply] at h2
  exact sub_eq_zero.mp h2

noncomputable abbrev pd (a : I ⊕ J) : Module.End K (MvPolynomial (I ⊕ J) K) :=
  (pderiv a).toLinearMap

theorem commute_pd (a b : I ⊕ J) : Commute (pd (K := K) a) (pd b) := by
  apply LinearMap.ext
  intro p
  exact pderiv_comm a b p

theorem commute_gdelta_pd (κ : I → J → K) (c : I ⊕ J) : Commute (gdelta κ) (pd c) := by
  unfold gdelta
  refine Commute.sum_left _ _ _ fun i _ => Commute.sum_left _ _ _ fun j _ => ?_
  refine Commute.smul_left ?_ _
  exact (commute_pd (Sum.inl i) c).mul_left (commute_pd (Sum.inr j) c)

theorem commute_gdelta_dL (κ : I → J → K) (i : I) : Commute (gdelta κ) (dL κ i) := by
  unfold dL
  refine Commute.sum_right _ _ _ fun j _ => ?_
  exact Commute.smul_right (commute_gdelta_pd κ (Sum.inr j)) _

theorem gdelta_dL_apply (κ : I → J → K) (i : I) (S : MvPolynomial (I ⊕ J) K) :
    gdelta κ (dL κ i S) = dL κ i (gdelta κ S) :=
  LinearMap.congr_fun (commute_gdelta_dL κ i).eq S

theorem gdelta_pow_succ_apply (κ : I → J → K) (m : ℕ) (S : MvPolynomial (I ⊕ J) K) :
    (gdelta κ ^ (m + 1)) S = gdelta κ ((gdelta κ ^ m) S) := by
  rw [pow_succ']
  rfl

theorem gdelta_apply (κ : I → J → K) (R : MvPolynomial (I ⊕ J) K) :
    gdelta κ R = ∑ i, ∑ j, κ i j • pderiv (Sum.inl i) (pderiv (Sum.inr j) R) := by
  simp [gdelta, LinearMap.sum_apply]

theorem dL_apply (κ : I → J → K) (i : I) (R : MvPolynomial (I ⊕ J) K) :
    dL κ i R = ∑ j, κ i j • pderiv (Sum.inr j) R := by
  simp [dL, LinearMap.sum_apply]

theorem gdelta_X_inl (κ : I → J → K) (i : I) (R : MvPolynomial (I ⊕ J) K) :
    gdelta κ (X (Sum.inl i) * R) = X (Sum.inl i) * gdelta κ R + dL κ i R := by
  classical
  have h1 : ∀ i' j, pderiv (Sum.inl i') (pderiv (Sum.inr j) (X (Sum.inl i) * R)) =
      X (Sum.inl i) * pderiv (Sum.inl i') (pderiv (Sum.inr j) R) +
        (if i' = i then pderiv (Sum.inr j) R else 0) := by
    intro i' j
    rw [pderiv_mul, pderiv_X_of_ne (by simp), zero_mul, zero_add, pderiv_mul, pderiv_X]
    by_cases h : i' = i
    · subst h
      simp [add_comm]
    · simp [h, Ne.symm h]
  rw [gdelta_apply, gdelta_apply, dL_apply]
  simp only [h1, smul_add, Finset.sum_add_distrib, Finset.mul_sum, mul_smul_comm, smul_ite,
    smul_zero]
  congr 1
  rw [Finset.sum_comm]
  simp

end

theorem commL_holds : CommL := by
  intro K I J _ _ _ κ i R n
  have h := ((commute_gdelta_dL κ i).pow_left n).eq
  exact LinearMap.congr_fun h R

theorem powXL_holds : PowXL := by
  intro K I J _ _ _ κ i R n
  induction n with
  | zero => simp [gdelta_X_inl]
  | succ n ih =>
    rw [gdelta_pow_succ_apply, ih, map_add, gdelta_X_inl, map_nsmul,
      ← gdelta_pow_succ_apply, gdelta_dL_apply,
      ← gdelta_pow_succ_apply, succ_nsmul _ (n + 1)]
    abel

section
variable {K I J : Type} [CommRing K] [Algebra ℚ K] [Fintype I] [Fintype J]

end

end PI.WickFormula.Gen
