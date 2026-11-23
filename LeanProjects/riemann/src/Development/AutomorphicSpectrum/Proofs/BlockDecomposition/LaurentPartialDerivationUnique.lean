import Mathlib
set_option backward.isDefEq.respectTransparency false

namespace GlobalTheory.CompanionTheory.ConeRes

open AddMonoidAlgebra

variable {K : Type} [Field K] {d : ℕ}

noncomputable def logDer (D : Derivation K (AddMonoidAlgebra K (Fin d →₀ ℤ))
    (AddMonoidAlgebra K (Fin d →₀ ℤ))) :
    (Fin d →₀ ℤ) →+ AddMonoidAlgebra K (Fin d →₀ ℤ) where
  toFun m := single (-m) 1 * D (single m 1)
  map_zero' := by
    have h : (single (0 : Fin d →₀ ℤ) (1 : K)) = 1 := one_def.symm
    rw [h, D.map_one_eq_zero, mul_zero]
  map_add' m n := by
    have h : (single (m + n) (1 : K)) = single m 1 * single n 1 := by
      rw [single_mul_single, one_mul]
    have hm : (single (-m) (1 : K)) * single m 1 = 1 := by
      rw [single_mul_single, one_mul, neg_add_cancel, one_def]
    have hn : (single (-n) (1 : K)) * single n 1 = 1 := by
      rw [single_mul_single, one_mul, neg_add_cancel, one_def]
    have hs : (single (-(m + n)) (1 : K)) = single (-m) 1 * single (-n) 1 := by
      rw [single_mul_single, one_mul, neg_add]
    rw [h, D.leibniz, hs]
    simp only [smul_eq_mul]
    linear_combination (single (-n) (1 : K) * D (single n 1)) * hm +
      (single (-m) (1 : K) * D (single m 1)) * hn

theorem logDer_apply (D : Derivation K (AddMonoidAlgebra K (Fin d →₀ ℤ))
    (AddMonoidAlgebra K (Fin d →₀ ℤ))) (m : Fin d →₀ ℤ) :
    logDer D m = single (-m) 1 * D (single m 1) := rfl

theorem derivation_single (k : Fin d)
    (D : Derivation K (AddMonoidAlgebra K (Fin d →₀ ℤ)) (AddMonoidAlgebra K (Fin d →₀ ℤ)))
    (hD : ∀ j : Fin d, D (single (Finsupp.single j 1) 1) = if j = k then 1 else 0)
    (m : Fin d →₀ ℤ) :
    D (single m 1) = (m k) • single (m - Finsupp.single k 1) (1 : K) := by
  have key : logDer D = (zmultiplesHom (AddMonoidAlgebra K (Fin d →₀ ℤ))
      (single (-Finsupp.single k 1) (1 : K))).comp (Finsupp.applyAddHom k) := by
    refine Finsupp.addHom_ext' fun j => AddMonoidHom.ext_int ?_
    simp only [AddMonoidHom.comp_apply, Finsupp.singleAddHom_apply, logDer_apply, hD,
      Finsupp.applyAddHom_apply, zmultiplesHom_apply]
    by_cases hj : j = k
    · subst hj
      simp
    · simp [hj]
  have hm : (single m (1 : K)) * single (-m) 1 = 1 := by
    rw [single_mul_single, one_mul, add_neg_cancel, one_def]
  have h1 : logDer D m = (m k) • single (-Finsupp.single k 1) (1 : K) := by
    rw [key]
    simp
  calc D (single m 1) = single m 1 * logDer D m := by
        rw [logDer_apply, ← mul_assoc, hm, one_mul]
    _ = _ := by
        rw [h1, mul_smul_comm, single_mul_single, one_mul, sub_eq_add_neg]

noncomputable def res (K : Type) [Field K] (d : ℕ) :
    AddMonoidAlgebra K (Fin d →₀ ℤ) →ₗ[K] K :=
  (Finsupp.lapply (-(∑ j : Fin d, Finsupp.single j (1 : ℤ)))) ∘ₗ
    (coeffLinearEquiv K).toLinearMap

theorem res_single (m : Fin d →₀ ℤ) (c : K) :
    res K d (single m c) = if m = -(∑ j : Fin d, Finsupp.single j 1) then c else 0 := by
  simp [res, Finsupp.single_apply]

theorem res_derivation_eq_zero (k : Fin d)
    (D : Derivation K (AddMonoidAlgebra K (Fin d →₀ ℤ)) (AddMonoidAlgebra K (Fin d →₀ ℤ)))
    (hD : ∀ j : Fin d, D (single (Finsupp.single j 1) 1) = if j = k then 1 else 0)
    (a : AddMonoidAlgebra K (Fin d →₀ ℤ)) : res K d (D a) = 0 := by
  induction a using AddMonoidAlgebra.induction_linear with
  | zero => simp
  | add x y hx hy => simp [hx, hy]
  | single m c =>
    have hc : (single m c : AddMonoidAlgebra K (Fin d →₀ ℤ)) = c • single m (1 : K) := by
      rw [smul_single, smul_eq_mul, mul_one]
    have hres : res K d (single (m - Finsupp.single k 1) (1 : K)) * ((m k : ℤ) : K) = 0 := by
      rw [res_single]
      split_ifs with h
      · have hmk : m k = 0 := by
          have h' := DFunLike.congr_fun h k
          simp [Finsupp.finset_sum_apply, Finsupp.single_apply] at h'
          omega
        simp [hmk]
      · simp
    rw [hc, D.map_smul, derivation_single k D hD m, map_smul, ← Int.cast_smul_eq_zsmul K, map_smul,
      smul_eq_mul, smul_eq_mul, mul_comm ((m k : ℤ) : K), hres, mul_zero]

theorem exists_res (K : Type) [Field K] (d : ℕ) :
    ∃ res : AddMonoidAlgebra K (Fin d →₀ ℤ) →ₗ[K] K,
      (∀ (m : Fin d →₀ ℤ) (c : K), res (AddMonoidAlgebra.single m c) =
        if m = -(∑ j : Fin d, Finsupp.single j 1) then c else 0) ∧
      ∀ (k : Fin d) (D : Derivation K (AddMonoidAlgebra K (Fin d →₀ ℤ))
          (AddMonoidAlgebra K (Fin d →₀ ℤ))),
        (∀ j : Fin d, D (AddMonoidAlgebra.single (Finsupp.single j 1) 1) =
          if j = k then 1 else 0) →
        ∀ a : AddMonoidAlgebra K (Fin d →₀ ℤ), res (D a) = 0 :=
  ⟨res K d, res_single, fun k D hD a => res_derivation_eq_zero k D hD a⟩

end GlobalTheory.CompanionTheory.ConeRes
