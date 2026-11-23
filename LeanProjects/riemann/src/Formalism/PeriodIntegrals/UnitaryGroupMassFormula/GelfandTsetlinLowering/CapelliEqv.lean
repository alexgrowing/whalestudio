import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GelfandTsetlinLowering.CapelliOps
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.HighestWeightIrreducible.ConstructionA

noncomputable section

namespace PI.WGL

open Formalism.BasicNotions Formalism.GradedWeylDivisibility MvPolynomial

theorem embGL_cc {n : ℕ} (g : GL (Fin n) ℂ) (i j : Fin n) :
    (embGL ℂ n (n + 1) rfl g : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (Fin.castSucc i) (Fin.castSucc j) = g i j := by
  simp [embGL, blkHom, Matrix.coe_reindexAlgEquiv, Matrix.reindex_apply, Matrix.submatrix_apply]

theorem embGL_lc {n : ℕ} (g : GL (Fin n) ℂ) (j : Fin n) :
    (embGL ℂ n (n + 1) rfl g : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (Fin.last n) (Fin.castSucc j) = 0 := by
  simp [embGL, blkHom, Matrix.coe_reindexAlgEquiv, Matrix.reindex_apply, Matrix.submatrix_apply]

theorem embGL_cl {n : ℕ} (g : GL (Fin n) ℂ) (i : Fin n) :
    (embGL ℂ n (n + 1) rfl g : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (Fin.castSucc i) (Fin.last n) = 0 := by
  simp [embGL, blkHom, Matrix.coe_reindexAlgEquiv, Matrix.reindex_apply, Matrix.submatrix_apply]

theorem embGL_ll {n : ℕ} (g : GL (Fin n) ℂ) :
    (embGL ℂ n (n + 1) rfl g : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (Fin.last n) (Fin.last n) = 1 := by
  simp [embGL, blkHom, Matrix.coe_reindexAlgEquiv, Matrix.reindex_apply, Matrix.submatrix_apply]

def lmapPoly {σ τ : Type} (φ : MvPolynomial σ ℂ →ₗ[ℂ] MvPolynomial τ ℂ) (p : Polynomial (MvPolynomial σ ℂ)) :
    Polynomial (MvPolynomial τ ℂ) :=
  ∑ k ∈ Finset.range (p.natDegree + 1), Polynomial.C (φ (p.coeff k)) * Polynomial.X ^ k

theorem lmapPoly_coeff {σ τ : Type} (φ : MvPolynomial σ ℂ →ₗ[ℂ] MvPolynomial τ ℂ)
    (p : Polynomial (MvPolynomial σ ℂ)) (k : ℕ) : (lmapPoly φ p).coeff k = φ (p.coeff k) := by
  simp only [lmapPoly, Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul_X_pow]
  rw [Finset.sum_ite_eq]
  split_ifs with hk
  · rfl
  · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by simp at hk; omega), map_zero]

theorem lmapPoly_eval {σ τ : Type} (φ : MvPolynomial σ ℂ →ₗ[ℂ] MvPolynomial τ ℂ)
    (p : Polynomial (MvPolynomial σ ℂ)) (t : ℂ) : (lmapPoly φ p).eval (C t) = φ (p.eval (C t)) := by
  rw [Polynomial.eval_eq_sum_range (p := p), lmapPoly, Polynomial.eval_finsetSum, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X, ← C_pow]
  rw [mul_comm (φ _), mul_comm (p.coeff i), ← smul_eq_C_mul, ← smul_eq_C_mul, map_smul]

theorem det_one_add_single {n : ℕ} (a b : Fin n) (t : ℂ) :
    (1 + Matrix.single a b t).det = if a = b then t + 1 else 1 := by
  by_cases hab : a = b
  · subst hab
    have hD : (1 + Matrix.single a a t) = Matrix.diagonal (fun i => if i = a then 1 + t else 1) := by
      ext i j
      by_cases hij : i = j
      · subst hij; by_cases hia : i = a
        · subst hia; simp
        · simp [hia, Ne.symm hia]
      · simp [hij, Matrix.single_apply]
        intro h1 h2; exact absurd (h1.symm.trans h2) hij
    rw [hD, Matrix.det_diagonal, Finset.prod_ite_eq']
    simp [add_comm]
  · have := Matrix.det_transvection_of_ne a b hab t
    unfold Matrix.transvection at this
    rw [this, if_neg hab]

theorem embGL_transvec {n : ℕ} (g : GL (Fin n) ℂ) (a b : Fin n) (t : ℂ)
    (hg : (g : Matrix (Fin n) (Fin n) ℂ) = 1 + Matrix.single a b t) :
    ((embGL ℂ n (n + 1) rfl g : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)).transpose =
      1 + Matrix.single b.castSucc a.castSucc t := by
  ext i j
  induction i using Fin.lastCases with
  | last =>
    induction j using Fin.lastCases with
    | last => simp [Matrix.transpose_apply, embGL_ll, Matrix.single_apply]
    | cast j =>
      simp [Matrix.transpose_apply, embGL_cl, Matrix.one_apply]
      exact fun h => Fin.castSucc_ne_last j h.symm
  | cast i =>
    induction j using Fin.lastCases with
    | last => simp [Matrix.transpose_apply, embGL_lc, Matrix.single_apply, Matrix.one_apply]
    | cast j =>
      rw [Matrix.transpose_apply, embGL_cc, hg]
      simp [Matrix.single_apply, Matrix.one_apply, eq_comm, and_comm]

theorem eqv_pol {n N : ℕ} (h : n + 1 = N) (mu : DomWeight n) (lam : DomWeight N)
    (φ : MvPolynomial (Fin n × Fin n) ℂ →ₗ[ℂ] MvPolynomial (Fin N × Fin N) ℂ) (hφ : IsEqv h mu lam φ)
    (a b : Fin n) (s : MvPolynomial (Fin n × Fin n) ℂ) (hs : s ∈ nablaSq ℂ n mu) :
    φ (pol ℂ a b s) + (if a = b then (mu.detShift : ℂ) • φ s else 0) =
      pol ℂ (Fin.castLE (by omega) a) (Fin.castLE (by omega) b) (φ s) +
        (if a = b then (lam.detShift : ℂ) • φ s else 0) := by
  subst h
  have hι : ∀ x : Fin n, Fin.castLE (by omega : n ≤ n + 1) x = Fin.castSucc x := fun x => Fin.ext rfl
  rw [hι a, hι b]
  set d1 := mu.detShift with hd1
  set d2 := lam.detShift with hd2
  set K : ℤ := |d1| + |d2| with hK
  have hK1 : 0 ≤ d1 + K := by have := neg_abs_le d1; have := abs_nonneg d2; omega
  have hK2 : 0 ≤ d2 + K := by have := neg_abs_le d2; have := abs_nonneg d1; omega
  set e1 := (d1 + K).toNat with he1d
  set e2 := (d2 + K).toNat with he2d
  have he1 : (e1 : ℤ) = d1 + K := Int.toNat_of_nonneg hK1
  have he2 : (e2 : ℤ) = d2 + K := Int.toNat_of_nonneg hK2
  set Q : Polynomial (MvPolynomial (Fin (n + 1) × Fin (n + 1)) ℂ) :=
    if a = b then Polynomial.X + 1 else 1 with hQ
  set P := Q ^ e1 * lmapPoly φ (rowGen ℂ a b s) - Q ^ e2 * rowGen ℂ a.castSucc b.castSucc (φ s) with hP
  have key : ∀ t : ℕ, P.eval (C (t : ℂ)) ∈ (⊥ : Submodule ℂ (MvPolynomial (Fin (n + 1) × Fin (n + 1)) ℂ)) := by
    intro t
    rw [Submodule.mem_bot]
    set D : ℂ := if a = b then (t : ℂ) + 1 else 1 with hD
    let g := Matrix.GeneralLinearGroup.mkOfDetNeZero _ (PI.WHw.det_one_add_single_ne a b t)
    have hgv : (g : Matrix (Fin n) (Fin n) ℂ) = 1 + Matrix.single a b (t : ℂ) := rfl
    have hgT : (g : Matrix (Fin n) (Fin n) ℂ).transpose = 1 + Matrix.single b a (t : ℂ) := by
      rw [hgv, Matrix.transpose_add, Matrix.transpose_one, Matrix.transpose_single]
    have hgT' := embGL_transvec g a b t hgv
    have hu : ((Matrix.GeneralLinearGroup.det g : ℂˣ) : ℂ) = D := by
      rw [Matrix.GeneralLinearGroup.val_det_apply, hgv, det_one_add_single]
    have hu' : ((Matrix.GeneralLinearGroup.det (embGL ℂ n (n + 1) rfl g) : ℂˣ) : ℂ) = D := by
      rw [Matrix.GeneralLinearGroup.val_det_apply, ← Matrix.det_transpose, hgT', det_one_add_single]
      rcases eq_or_ne a b with hab | hab
      · subst hab; simp [hD]
      · simp [hD, hab, Ne.symm hab]
    have huu : Matrix.GeneralLinearGroup.det (embGL ℂ n (n + 1) rfl g) = Matrix.GeneralLinearGroup.det g :=
      Units.ext (hu'.trans hu.symm)
    have heq := hφ.2 g s hs
    unfold sqAct detPow at heq
    rw [hgT, hgT', huu, map_smul, ← PI.WHw.eval_rowGen, ← PI.WHw.eval_rowGen] at heq
    set u := Matrix.GeneralLinearGroup.det g
    have heq2 := congrArg (fun x => ((u ^ K : ℂˣ) : ℂ) • x) heq
    simp only [smul_smul, ← Units.val_mul, ← zpow_add] at heq2
    rw [show K + mu.detShift = (e1 : ℤ) by omega, show K + lam.detShift = (e2 : ℤ) by omega,
      zpow_natCast, zpow_natCast, Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val, hu] at heq2
    have hQe : Q.eval (C (t : ℂ)) = C D := by
      rw [hQ, hD]; split_ifs <;> simp
    rw [hP, Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_mul, Polynomial.eval_pow,
      Polynomial.eval_pow, hQe, lmapPoly_eval, ← C_pow, ← C_pow, ← smul_eq_C_mul, ← smul_eq_C_mul, heq2, sub_self]
  have h1 := PI.WHw.coeff_mem_of_eval ⊥ P key 1
  rw [Submodule.mem_bot] at h1
  have hL0 : (lmapPoly φ (rowGen ℂ a b s)).coeff 0 = φ s := by
    rw [lmapPoly_coeff, rowGen_coeff_zero]
  have hL1 : (lmapPoly φ (rowGen ℂ a b s)).coeff 1 = φ (pol ℂ a b s) := by
    rw [lmapPoly_coeff, pol_eq_rowDiv]; rfl
  have hG0 : (rowGen ℂ a.castSucc b.castSucc (φ s)).coeff 0 = φ s := rowGen_coeff_zero ℂ _ _ _
  have hG1 : (rowGen ℂ a.castSucc b.castSucc (φ s)).coeff 1 = pol ℂ a.castSucc b.castSucc (φ s) := by
    rw [pol_eq_rowDiv]; rfl
  have hc1 : ∀ (e : ℕ) (F : Polynomial (MvPolynomial (Fin (n + 1) × Fin (n + 1)) ℂ)),
      (Q ^ e * F).coeff 1 = F.coeff 1 + (if a = b then (e : MvPolynomial _ ℂ) * F.coeff 0 else 0) := by
    intro e F
    rw [hQ]
    split_ifs with hab
    · rw [Polynomial.coeff_mul, Finset.Nat.sum_antidiagonal_succ, Finset.Nat.antidiagonal_zero,
        Finset.sum_singleton, Polynomial.coeff_X_add_one_pow, Polynomial.coeff_X_add_one_pow]
      simp
    · simp
  rw [hP, Polynomial.coeff_sub, hc1, hc1, hL0, hL1, hG0, hG1] at h1
  by_cases hab : a = b
  · simp only [hab, if_true] at h1 ⊢
    have c1 : ((e1 : ℕ) : MvPolynomial (Fin (n + 1) × Fin (n + 1)) ℂ) = C ((d1 : ℂ) + (K : ℂ)) := by
      rw [← map_natCast C]; congr 1; exact_mod_cast he1
    have c2 : ((e2 : ℕ) : MvPolynomial (Fin (n + 1) × Fin (n + 1)) ℂ) = C ((d2 : ℂ) + (K : ℂ)) := by
      rw [← map_natCast C]; congr 1; exact_mod_cast he2
    rw [c1, c2, map_add, map_add] at h1
    rw [smul_eq_C_mul, smul_eq_C_mul]
    subst hab
    linear_combination h1
  · simp only [hab, if_false, add_zero] at h1 ⊢
    exact sub_eq_zero.mp h1

end PI.WGL
