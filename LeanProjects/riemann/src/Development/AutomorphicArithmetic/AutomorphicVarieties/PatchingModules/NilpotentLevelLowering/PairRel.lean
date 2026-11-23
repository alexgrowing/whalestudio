import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.NilpotentLevelLowering.ActUVariableEqPow
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ExistsDiagonalization
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N ValuativeRel IsLocalRing
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil
open UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Hi UpperTheory.V.AlgebraTools UpperTheory.V.Pa UpperTheory.V.Pa.Lev
open scoped TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private theorem prod_conj {K : Type} [Field K] {n : ℕ} (V : Matrix (Fin n) (Fin n) K) :
    ∀ (m : ℕ) (F : Fin m → Matrix (Fin n) (Fin n) K) (d : Fin m → Fin n → K),
      (∀ k, F k * V = V * Matrix.diagonal (d k)) →
      (List.ofFn F).prod * V = V * Matrix.diagonal (fun j => ∏ k, d k j) := by
  intro m
  induction m with
  | zero => intro F d _; simp
  | succ m ih =>
    intro F d h
    rw [List.ofFn_succ, List.prod_cons, mul_assoc, ih (fun k => F k.succ) (fun k => d k.succ) (fun k => h _),
      ← mul_assoc, h 0, mul_assoc, Matrix.diagonal_mul_diagonal]
    simp only [Fin.prod_univ_succ]

private theorem exists_diag {K : Type} [Field K] {n : ℕ} (P : Matrix (Fin n) (Fin n) K) (α : Fin n → K)
    (hα : Function.Injective α)
    (hP : P.charpoly = ∏ i, (Polynomial.X - Polynomial.C (α i))) :
    ∃ V : Matrix (Fin n) (Fin n) K, IsUnit V ∧ P * V = V * Matrix.diagonal α :=
  _root_.UpperTheory.Reformulated.B.ExistsDiagonalization.exists_diag P α hα hP

theorem UpperTheory.V.Pa.Lev.pairRel :
    ∀ (K : Type) [Field K] (n : ℕ) (P T : Matrix (Fin n) (Fin n) K) (α β : Fin n → K), Function.Injective α → P * T = T * P → P.charpoly = ∏ i, (Polynomial.X - Polynomial.C (α i)) → (∀ a : ℕ, (P ^ a * T).trace = ∑ i, α i ^ a * β i) → ∀ i, (List.ofFn fun i' => if i' = i then 1 else P - α i' • (1 : Matrix (Fin n) (Fin n) K)).prod * (T - β i • (1 : Matrix (Fin n) (Fin n) K)) = 0 := by
  intro K _ n P T α β hα hc hP htr i
  obtain ⟨V, hV, hPV⟩ := exists_diag P α hα hP
  obtain ⟨V', h1, h2⟩ := isUnit_iff_exists.1 hV
  obtain ⟨S, hS⟩ : ∃ S, S = V' * T * V := ⟨_, rfl⟩
  have hTV : T * V = V * S := by
    rw [hS, ← mul_assoc, ← mul_assoc, h1, one_mul]
  have hSD : Matrix.diagonal α * S = S * Matrix.diagonal α := by
    refine hV.mul_left_cancel ?_
    rw [← mul_assoc, ← hPV, mul_assoc, ← hTV, ← mul_assoc, hc, mul_assoc, hPV, ← mul_assoc, hTV,
      mul_assoc]
  have hSd : S = Matrix.diagonal (fun j => S j j) := by
    ext a b
    by_cases hab : a = b
    · subst hab; simp
    · rw [Matrix.diagonal_apply_ne _ hab]
      have := congrFun (congrFun hSD a) b
      rw [Matrix.diagonal_mul, Matrix.mul_diagonal, mul_comm] at this
      by_contra h0
      exact hab (hα (mul_left_cancel₀ h0 this))
  have hpow : ∀ a : ℕ, P ^ a * V = V * Matrix.diagonal α ^ a := by
    intro a
    induction a with
    | zero => simp
    | succ a ih => rw [pow_succ, mul_assoc, hPV, ← mul_assoc, ih, mul_assoc, ← pow_succ]
  have htr' : ∀ a : ℕ, ∑ j, α j ^ a * S j j = ∑ j, α j ^ a * β j := by
    intro a
    rw [← htr a]
    have e : P ^ a * T = V * (Matrix.diagonal α ^ a * S) * V' := by
      rw [← mul_assoc, ← hpow, mul_assoc (P ^ a), ← hTV, mul_assoc, mul_assoc, h1, mul_one]
    rw [e, Matrix.trace_mul_cycle, h2, one_mul, Matrix.diagonal_pow]
    simp [Matrix.trace, Matrix.diagonal_mul]
  have hβ : (fun j => S j j - β j) = 0 := by
    refine Matrix.eq_zero_of_forall_pow_sum_mul_pow_eq_zero hα (fun a => ?_)
    simp only [sub_mul, Finset.sum_sub_distrib, sub_eq_zero]
    simpa only [mul_comm] using htr' a
  have hSβ : S = Matrix.diagonal β := by
    rw [hSd]
    congr 1
    ext j
    exact sub_eq_zero.1 (congrFun hβ j)
  have hE := prod_conj V n
    (fun i' => if i' = i then 1 else P - α i' • (1 : Matrix (Fin n) (Fin n) K))
    (fun k j => if k = i then 1 else α j - α k) (by
      intro k
      by_cases hk : k = i
      · simp [hk]
      · simp only [if_neg hk]
        rw [sub_mul, hPV, smul_mul_assoc, one_mul]
        ext a b
        simp [Matrix.mul_diagonal, mul_sub, mul_comm])
  have hT : (T - β i • (1 : Matrix (Fin n) (Fin n) K)) * V = V * Matrix.diagonal (fun j => β j - β i) := by
    rw [sub_mul, hTV, hSβ, smul_mul_assoc, one_mul]
    ext a b
    simp [Matrix.mul_diagonal, mul_sub, mul_comm]
  refine hV.mul_right_cancel ?_
  rw [mul_assoc, hT, ← mul_assoc, hE, mul_assoc, Matrix.diagonal_mul_diagonal, zero_mul]
  have : (fun j => (∏ k, if k = i then 1 else α j - α k) * (β j - β i)) = fun _ => (0 : K) := by
    ext j
    by_cases hj : j = i
    · simp [hj]
    · rw [Finset.prod_eq_zero (Finset.mem_univ j) (by simp [hj]), zero_mul]
  rw [this, Matrix.diagonal_zero, mul_zero]
