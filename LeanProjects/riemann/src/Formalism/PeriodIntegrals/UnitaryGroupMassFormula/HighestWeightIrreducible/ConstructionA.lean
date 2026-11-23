import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.HighestWeightIrreducible.ClosedEqNablaC

noncomputable section

namespace PI.WHw

open Formalism.BasicNotions Formalism.GradedWeylDivisibility MvPolynomial

theorem coeff_mem_of_eval {σ : Type*} (U : Submodule ℂ (MvPolynomial σ ℂ))
    (p : Polynomial (MvPolynomial σ ℂ))
    (h : ∀ n : ℕ, p.eval (C (n : ℂ)) ∈ U) (k : ℕ) : p.coeff k ∈ U := by
  classical
  rw [← Submodule.Quotient.mk_eq_zero, ← Module.forall_dual_apply_eq_zero_iff ℂ]
  intro φ
  obtain ⟨q, hq⟩ : ∃ q : Polynomial ℂ, q = ∑ i ∈ Finset.range (p.natDegree + 1),
      Polynomial.C ((φ.comp U.mkQ) (p.coeff i)) * Polynomial.X ^ i := ⟨_, rfl⟩
  have hroot : ∀ n : ℕ, q.eval (n : ℂ) = 0 := by
    intro n
    have h1 : (φ.comp U.mkQ) (p.eval (C (n : ℂ))) = 0 := by
      rw [LinearMap.comp_apply, Submodule.mkQ_apply, (Submodule.Quotient.mk_eq_zero U).mpr (h n), map_zero]
    rw [Polynomial.eval_eq_sum_range, map_sum] at h1
    rw [hq, Polynomial.eval_finset_sum, ← h1]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X, ← MvPolynomial.C_pow,
      mul_comm (p.coeff i), ← MvPolynomial.smul_eq_C_mul, map_smul, smul_eq_mul, mul_comm]
  by_cases hk : k ≤ p.natDegree
  · have hq0 : q = 0 := Polynomial.eq_zero_of_infinite_isRoot q
      (Set.infinite_of_injective_forall_mem Nat.cast_injective (fun n => hroot n))
    have hc := congrArg (fun r => Polynomial.coeff r k) hq0
    simp only [hq, Polynomial.finset_sum_coeff, Polynomial.coeff_C_mul_X_pow, Polynomial.coeff_zero,
      Finset.sum_ite_eq, Finset.mem_range, Nat.lt_succ_iff.mpr hk, if_true] at hc
    simpa using hc
  · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)]
    simp

private theorem eval_rowGen_X_eq_rowAct_one_add_single {N n : ℕ} (a b : Fin N) (t : ℂ) (i : Fin N) (j : Fin n) :
    (rowGen ℂ a b (X (i, j) : MvPolynomial (Fin N × Fin n) ℂ)).eval (C t) =
      rowAct ℂ (1 + Matrix.single b a t) (X (i, j) : MvPolynomial (Fin N × Fin n) ℂ) := by
  have hterm : ∀ c : Fin N, C ((1 + Matrix.single b a t) i c) * (X (c, j) : MvPolynomial (Fin N × Fin n) ℂ) =
      (if c = i then X (i, j) else 0) + (if c = a then (if i = b then C t * X (a, j) else 0) else 0) := by
    intro c
    simp only [Matrix.add_apply, Matrix.one_apply, Matrix.single_apply, ite_and]
    split_ifs <;> subst_vars <;> simp_all [add_mul]
  simp only [rowGen, rowAct, MvPolynomial.aeval_X, hterm, Finset.sum_add_distrib, Finset.sum_ite_eq',
    Finset.mem_univ, if_true]
  by_cases h : i = b
  · simp [h]
    ring
  · simp [h]

theorem eval_rowGen {N n : ℕ} (a b : Fin N) (t : ℂ) (f : MvPolynomial (Fin N × Fin n) ℂ) :
    (rowGen ℂ a b f).eval (C t) = rowAct ℂ (1 + Matrix.single b a t) f := by
  induction f using MvPolynomial.induction_on
  · rename_i c
    simp [rowGen, rowAct]
  · rename_i p q hp hq
    simp only [map_add, Polynomial.eval_add, hp, hq]
  · rename_i p v hp
    obtain ⟨i, j⟩ := v
    simp only [map_mul, Polynomial.eval_mul, hp, eval_rowGen_X_eq_rowAct_one_add_single]

theorem det_one_add_single_ne {N : ℕ} (a b : Fin N) (n : ℕ) :
    (1 + Matrix.single a b (n : ℂ)).det ≠ 0 := by
  by_cases h : a = b
  · subst h
    have hd : (1 + Matrix.single a a (n : ℂ)) = Matrix.diagonal (fun i => if i = a then 1 + (n : ℂ) else 1) := by
      ext i j
      simp only [Matrix.add_apply, Matrix.one_apply, Matrix.single_apply, Matrix.diagonal_apply, ite_and]
      split_ifs <;> subst_vars <;> simp_all
    rw [hd, Matrix.det_diagonal, Finset.prod_ite_eq', if_pos (Finset.mem_univ a)]
    have h1 : ((n : ℂ) + 1) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero n
    rwa [add_comm] at h1
  · rw [show (1 + Matrix.single a b (n : ℂ)) = Matrix.transvection a b (n : ℂ) from rfl,
      Matrix.det_transvection_of_ne a b h]
    exact one_ne_zero

private theorem transpose_one_add_single {N : ℕ} (a b : Fin N) (c : ℂ) :
    (1 + Matrix.single a b c).transpose = 1 + Matrix.single b a c := by
  ext i j
  simp only [Matrix.transpose_apply, Matrix.add_apply, Matrix.one_apply, Matrix.single_apply, ite_and]
  split_ifs <;> subst_vars <;> simp_all

theorem stable_subspace_closed : StableClosedC := by
  intro N lam U _hU hstab a b k f hf
  show (rowGen ℂ a b f).coeff k ∈ U
  apply coeff_mem_of_eval U (rowGen ℂ a b f) _ k
  intro m
  rw [eval_rowGen]
  have hu : IsUnit (1 + Matrix.single a b (m : ℂ)) :=
    (Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr (det_one_add_single_ne a b m))
  have hg := hstab hu.unit f hf
  unfold Formalism.BasicNotions.sqAct at hg
  rw [hu.unit_spec, transpose_one_add_single] at hg
  have hc : Formalism.BasicNotions.detPow ℂ N hu.unit lam.detShift ≠ 0 := by
    unfold Formalism.BasicNotions.detPow
    exact Units.ne_zero _
  have h2 := U.smul_mem (Formalism.BasicNotions.detPow ℂ N hu.unit lam.detShift)⁻¹ hg
  rwa [inv_smul_smul₀ hc] at h2

theorem fixed_vectors_killed : FixedKilledC := by
  intro N lam f _hf hfix a b hab k hk
  have hne : a ≠ b := ne_of_lt hab
  have key : ∀ m : ℕ, (rowGen ℂ a b f - Polynomial.C f).eval (C (m : ℂ)) ∈
      (⊥ : Submodule ℂ (MvPolynomial (Fin N × Fin N) ℂ)) := by
    intro m
    rw [Submodule.mem_bot, Polynomial.eval_sub, Polynomial.eval_C, eval_rowGen, sub_eq_zero]
    have hdet : (1 + Matrix.single a b (m : ℂ)).det = 1 := Matrix.det_transvection_of_ne a b hne _
    have hu : IsUnit (1 + Matrix.single a b (m : ℂ)) :=
      (Matrix.isUnit_iff_isUnit_det _).mpr (by rw [hdet]; exact isUnit_one)
    have h1 := hfix hu.unit ?_ ?_
    · unfold Formalism.BasicNotions.sqAct at h1
      rw [hu.unit_spec, transpose_one_add_single] at h1
      have hd1 : Formalism.BasicNotions.detPow ℂ N hu.unit lam.detShift = 1 := by
        unfold Formalism.BasicNotions.detPow
        have h3 : Matrix.GeneralLinearGroup.det hu.unit = 1 := by
          apply Units.ext
          rw [Matrix.GeneralLinearGroup.val_det_apply, hu.unit_spec, hdet, Units.val_one]
        rw [h3, one_zpow, Units.val_one]
      rw [hd1, one_smul] at h1
      exact h1
    · intro i j hji
      rw [hu.unit_spec, Matrix.add_apply, Matrix.one_apply_ne (ne_of_lt hji).symm, zero_add]
      simp only [Matrix.single_apply]
      split_ifs with h
      · obtain ⟨rfl, rfl⟩ := h
        exact absurd (hab.trans hji) (lt_irrefl _)
      · rfl
    · intro i
      rw [hu.unit_spec, Matrix.add_apply, Matrix.one_apply_eq]
      simp only [Matrix.single_apply]
      split_ifs with h
      · exact absurd (h.1.trans h.2.symm) hne
      · simp
  have h4 := coeff_mem_of_eval ⊥ _ key k
  rw [Submodule.mem_bot, Polynomial.coeff_sub, Polynomial.coeff_C, if_neg (by omega), sub_zero] at h4
  exact h4

end PI.WHw
