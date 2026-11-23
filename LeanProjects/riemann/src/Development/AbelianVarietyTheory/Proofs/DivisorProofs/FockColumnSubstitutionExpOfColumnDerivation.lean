import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ColDerApply
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDensityOfImmersion
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegralDetCharacterFockColumnSubstitutionEqZero

noncomputable section

open MvPolynomial

namespace GlobalTheory.ColLie

open GlobalTheory.MinorFrame

variable {ι : Type} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in

theorem totalDegree_colSub_le {d a : ℕ} (g : ι → Matrix (Fin a) (Fin a) ℂ) (P : Pol ι d a) :
    (colSub g P).totalDegree ≤ P.totalDegree := by
  have hX : ∀ y : Var ι d a, (colSub g (X y : Pol ι d a)).totalDegree ≤ 1 := by
    intro y
    rw [colSub, aeval_X]
    refine (totalDegree_finset_sum _ _).trans (Finset.sup_le fun j _ => ?_)
    refine (totalDegree_mul _ _).trans ?_
    rw [totalDegree_C, totalDegree_X]
  conv_lhs => rw [as_sum P]
  rw [map_sum]
  refine (totalDegree_finset_sum _ _).trans (Finset.sup_le fun m hm => ?_)
  refine le_trans ?_ (le_totalDegree hm)
  rw [monomial_eq, map_mul, algHom_C, algebraMap_eq, Finsupp.prod, map_prod]
  refine (totalDegree_mul _ _).trans ?_
  rw [totalDegree_C, zero_add]
  refine (totalDegree_finset_prod _ _).trans (Finset.sum_le_sum fun y _ => ?_)
  rw [map_pow]
  refine (totalDegree_pow _ _).trans ?_
  simpa using Nat.mul_le_mul_left (m y) (hX y)

theorem hasDerivAt_dual_of_coeff {σ : Type} [Finite σ] (l : MvPolynomial σ ℂ →ₗ[ℂ] ℂ) (N : ℕ)
    (u : ℝ → MvPolynomial σ ℂ) (u' : MvPolynomial σ ℂ) (t : ℝ) (hu : ∀ s, (u s).totalDegree ≤ N)
    (hd : ∀ m, HasDerivAt (fun s => coeff m (u s)) (coeff m u') t) : HasDerivAt (fun s => l (u s)) (l u') t := by
  classical
  let A : Finset (σ →₀ ℕ) := (Finsupp.finite_of_degree_le (σ := σ) N).toFinset ∪ u'.support
  have key : ∀ P : MvPolynomial σ ℂ, P.support ⊆ A → l P = ∑ m ∈ A, coeff m P * l (monomial m 1) := by
    intro P hP
    conv_lhs => rw [as_sum P]
    rw [map_sum]
    refine Finset.sum_subset_zero_on_sdiff hP (fun m hm => ?_) (fun m _ => ?_)
    · rw [notMem_support_iff.1 (Finset.mem_sdiff.1 hm).2, zero_mul]
    · rw [← smul_eq_mul, ← map_smul, smul_monomial, smul_eq_mul, mul_one]
  have h1 : ∀ s, (u s).support ⊆ A := by
    intro s m hm
    refine Finset.mem_union_left _ ?_
    rw [Set.Finite.mem_toFinset]
    exact (le_totalDegree hm).trans (hu s)
  rw [key u' Finset.subset_union_right, funext fun s => key (u s) (h1 s)]
  exact HasDerivAt.fun_sum fun m _ => (hd m).mul_const _

omit [Fintype ι] in
theorem atPl_mul {a : ℕ} (τ : ι) (A B : Matrix (Fin a) (Fin a) ℂ) :
    atPl τ (A * B) = fun σ => atPl τ A σ * atPl τ B σ := by
  funext σ
  by_cases h : σ = τ
  · subst h; simp [atPl]
  · simp [atPl, h]

theorem colSub_atPl_one {d a : ℕ} (τ : ι) (P : Pol ι d a) : colSub (atPl τ 1) P = P := by
  have : (colSub (atPl τ 1) : Pol ι d a →ₐ[ℂ] Pol ι d a) = AlgHom.id ℂ _ := by
    refine algHom_ext fun v => ?_
    have h1 : atPl τ (1 : Matrix (Fin a) (Fin a) ℂ) v.1 = 1 := by
      by_cases h : v.1 = τ
      · rw [h]; simp [atPl]
      · simp [atPl, h]
    rw [colSub, aeval_X, h1, Finset.sum_eq_single v.2.2]
    · simp
    · intro b _ hb
      rw [Matrix.one_apply_ne hb]
      simp
    · simp
  rw [this, AlgHom.id_apply]

theorem colSub_exp_of_colDer : ∀ {ι : Type} [Fintype ι] [DecidableEq ι] (d a : ℕ) (τ : ι) (c : ℕ) (Q : Type) [AddCommGroup Q] [Module ℂ Q]
    (q : GlobalTheory.MinorFrame.Pol ι d a →ₗ[ℂ] Q),
    (∀ (S : Matrix (Fin a) (Fin a) ℂ) (R : GlobalTheory.MinorFrame.Pol ι d a) (m : GlobalTheory.MinorFrame.Var ι d a →₀ ℕ),
      HasDerivAt (fun h : ℝ => MvPolynomial.coeff m (GlobalTheory.MinorFrame.colSub (GlobalTheory.ColLie.atPl τ (NormedSpace.exp ((h : ℂ) • S))) R))
        (MvPolynomial.coeff m (GlobalTheory.ColLie.colDer τ S R)) 0) →
    (∀ S : Matrix (Fin a) (Fin a) ℂ, S.conjTranspose = -S → ∀ P, q (GlobalTheory.ColLie.colDer τ S P) = ((c : ℂ) * S.trace) • q P) →
    ∀ S : Matrix (Fin a) (Fin a) ℂ, S.conjTranspose = -S → ∀ P,
      q (GlobalTheory.MinorFrame.colSub (GlobalTheory.ColLie.atPl τ (NormedSpace.exp S)) P) = ((NormedSpace.exp S).det ^ c) • q P := by
  intro ι _ _ d a τ c Q _ _ q hco hq S hS P
  rw [← sub_eq_zero, ← Module.forall_dual_apply_eq_zero_iff ℂ]
  intro l
  rw [map_sub, map_smul, sub_eq_zero, smul_eq_mul]
  set k : ℂ := (c : ℂ) * S.trace with hk
  let R : ℝ → Pol ι d a := fun t => colSub (atPl τ (NormedSpace.exp ((t : ℂ) • S))) P
  let f : ℝ → ℂ := fun t => l (q (R t))
  have hadd : ∀ s t : ℝ, colSub (atPl τ (NormedSpace.exp ((s : ℂ) • S))) (R t) = R (s + t) := by
    intro s t
    simp only [R]
    rw [← colSub_mul, ← atPl_mul, Complex.ofReal_add, add_smul,
      Matrix.exp_add_of_commute _ _ (((Commute.refl S).smul_left _).smul_right _)]
  have hd : ∀ t, HasDerivAt f (f t * k) t := by
    intro t
    have h0 := hasDerivAt_dual_of_coeff (l ∘ₗ q) (R t).totalDegree
      (fun h : ℝ => colSub (atPl τ (NormedSpace.exp ((h : ℂ) • S))) (R t)) (colDer τ S (R t)) 0
      (fun s => totalDegree_colSub_le _ _) (hco S (R t))
    simp only [hadd, LinearMap.comp_apply, hq S hS, map_smul, smul_eq_mul] at h0
    rw [← sub_self t] at h0
    have h1 := h0.comp_sub_const t t
    simp only [sub_add_cancel] at h1
    rw [mul_comm]
    exact h1
  have hg : ∀ t : ℝ, HasDerivAt (fun s : ℝ => f s * Complex.exp (-(s * k))) 0 t := by
    intro t
    have h1 : HasDerivAt (fun s : ℝ => -((s : ℂ) * k)) (-k) t := by
      simpa using ((Complex.ofRealCLM.hasDerivAt (x := t)).mul_const k).fun_neg
    exact ((hd t).fun_mul h1.cexp).congr_deriv (by ring)
  have hc := is_const_of_deriv_eq_zero (fun t => (hg t).differentiableAt) (fun t => (hg t).deriv) 1 0
  simp only [f, R, Complex.ofReal_one, Complex.ofReal_zero, one_smul, zero_smul, NormedSpace.exp_zero, colSub_atPl_one,
    one_mul, zero_mul, neg_zero, Complex.exp_zero, mul_one] at hc
  rw [← hc, GlobalTheory.SUVol.det_exp, ← Complex.exp_nat_mul, ← hk, mul_comm, mul_assoc, ← Complex.exp_add, neg_add_cancel,
    Complex.exp_zero, mul_one]

end GlobalTheory.ColLie

end
