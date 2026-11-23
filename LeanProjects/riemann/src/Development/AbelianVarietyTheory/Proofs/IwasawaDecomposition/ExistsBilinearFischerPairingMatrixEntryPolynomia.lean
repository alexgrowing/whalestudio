import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ColLieApply

noncomputable section

open MvPolynomial

namespace GlobalTheory.DefLift.BilFischer

variable {σ : Type} [Fintype σ]

def wt (α : σ →₀ ℕ) : ℂ := ∏ v, ((α v).factorial : ℂ)

theorem wt_ne_zero (α : σ →₀ ℕ) : wt α ≠ 0 :=
  Finset.prod_ne_zero_iff.2 fun v _ => Nat.cast_ne_zero.2 (Nat.factorial_ne_zero _)

theorem wt_zero : wt (0 : σ →₀ ℕ) = 1 := by simp [wt]

theorem wt_add_single (α : σ →₀ ℕ) (v : σ) : wt (α + Finsupp.single v 1) = wt α * ((α v : ℂ) + 1) := by
  classical
  unfold wt
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ v),
    ← Finset.mul_prod_erase _ (fun x => ((α x).factorial : ℂ)) (Finset.mem_univ v)]
  have h3 : ∏ x ∈ Finset.univ.erase v, (((α + Finsupp.single v 1 : σ →₀ ℕ) x).factorial : ℂ) =
      ∏ x ∈ Finset.univ.erase v, ((α x).factorial : ℂ) := by
    apply Finset.prod_congr rfl
    intro x hx
    have hxv : x ≠ v := Finset.ne_of_mem_erase hx
    simp [Finsupp.single_apply, Ne.symm hxv]
  rw [h3]
  simp only [Finsupp.add_apply, Finsupp.single_eq_same, Nat.factorial_succ]
  push_cast
  ring

def pair : MvPolynomial σ ℂ →ₗ[ℂ] MvPolynomial σ ℂ →ₗ[ℂ] ℂ :=
  (basisMonomials σ ℂ).constr ℂ fun α => wt α • lcoeff ℂ α

theorem pair_monomial_one (α : σ →₀ ℕ) (Q : MvPolynomial σ ℂ) :
    pair (monomial α 1) Q = wt α * coeff α Q := by
  have := (basisMonomials σ ℂ).constr_basis ℂ (fun α => wt α • lcoeff ℂ α) α
  rw [coe_basisMonomials] at this
  unfold pair
  rw [this]
  simp

theorem pair_monomial (α : σ →₀ ℕ) (c : ℂ) (Q : MvPolynomial σ ℂ) :
    pair (monomial α c) Q = c * (wt α * coeff α Q) := by
  have : (monomial α c : MvPolynomial σ ℂ) = c • monomial α 1 := by
    rw [smul_monomial, smul_eq_mul, mul_one]
  rw [this, map_smul, LinearMap.smul_apply, pair_monomial_one, smul_eq_mul]

theorem pair_mul_X (P Q : MvPolynomial σ ℂ) (v : σ) : pair (P * X v) Q = pair P (pderiv v Q) := by
  induction P using MvPolynomial.induction_on' with
  | monomial α c =>
    rw [X, monomial_mul, mul_one, pair_monomial, pair_monomial, coeff_pderiv, wt_add_single]
    ring
  | add P P' h h' => simp only [add_mul, map_add, LinearMap.add_apply, h, h']

def lin (A : σ → σ → ℂ) : MvPolynomial σ ℂ →ₐ[ℂ] MvPolynomial σ ℂ :=
  aeval fun v => ∑ w, A v w • X w

theorem lin_X (A : σ → σ → ℂ) (v : σ) : lin A (X v) = ∑ w, A v w • X w := by
  simp [lin]

theorem pderiv_lin_X (A : σ → σ → ℂ) (v u : σ) : pderiv v (lin A (X u)) = C (A u v) := by
  classical
  rw [lin_X, map_sum, Finset.sum_eq_single v]
  · simp [smul_eq_C_mul]
  · intro w _ hw
    simp [pderiv_X, Pi.single_apply, hw]
  · simp

theorem pderiv_lin (A : σ → σ → ℂ) (v : σ) (Q : MvPolynomial σ ℂ) :
    pderiv v (lin A Q) = ∑ w, A w v • lin A (pderiv w Q) := by
  classical
  induction Q using MvPolynomial.induction_on with
  | C c => simp [lin]
  | add P P' h h' => simp only [map_add, h, h', smul_add, Finset.sum_add_distrib]
  | mul_X P u h =>
    rw [map_mul, Derivation.leibniz, h, pderiv_lin_X]
    simp only [Derivation.leibniz, smul_eq_mul, map_add, map_mul, smul_add, Finset.sum_add_distrib,
      Finset.mul_sum, mul_smul_comm]
    congr 1
    rw [Finset.sum_eq_single u]
    · simp [smul_eq_C_mul, mul_comm]
    · intro w _ hw
      simp [pderiv_X, Pi.single_apply, hw, Ne.symm hw]
    · simp

theorem coeff_zero_lin (A : σ → σ → ℂ) (Q : MvPolynomial σ ℂ) : coeff 0 (lin A Q) = coeff 0 Q := by
  change constantCoeff (lin A Q) = constantCoeff Q
  induction Q using MvPolynomial.induction_on with
  | C c => simp [lin]
  | add P P' h h' => simp only [map_add, h, h']
  | mul_X P u h => simp [lin_X, map_sum, smul_eq_C_mul]

theorem pair_lin (A : σ → σ → ℂ) (P Q : MvPolynomial σ ℂ) :
    pair (lin A P) Q = pair P (lin (fun v w => A w v) Q) := by
  induction P using MvPolynomial.induction_on generalizing Q with
  | C c =>
    have : lin A (C c) = C c := by simp [lin]
    rw [this, C_apply, pair_monomial, pair_monomial, coeff_zero_lin]
  | add P P' h h' => simp only [map_add, LinearMap.add_apply, h, h']
  | mul_X P u h =>
    rw [pair_mul_X, pderiv_lin, map_mul, lin_X, Finset.mul_sum, map_sum, map_sum, LinearMap.sum_apply]
    refine Finset.sum_congr rfl fun w _ => ?_
    rw [mul_smul_comm, map_smul, map_smul, LinearMap.smul_apply, pair_mul_X, h]

theorem pair_nondeg (Q : MvPolynomial σ ℂ) (h : ∀ P, pair P Q = 0) : Q = 0 := by
  ext α
  have := h (monomial α 1)
  rw [pair_monomial_one] at this
  simpa [wt_ne_zero] using this

theorem pair_rep (ℓ : MvPolynomial σ ℂ →ₗ[ℂ] ℂ) (d : ℕ)
    (h : ∀ α : σ →₀ ℕ, d < α.degree → ℓ (monomial α 1) = 0) : ∃ Q, ∀ P, pair P Q = ℓ P := by
  classical
  have hfin : {α : σ →₀ ℕ | α.degree ≤ d}.Finite := Finsupp.finite_of_degree_le d
  refine ⟨∑ α ∈ hfin.toFinset, monomial α (ℓ (monomial α 1) / wt α), fun P => ?_⟩
  induction P using MvPolynomial.induction_on' with
  | monomial α c =>
    have : (monomial α c : MvPolynomial σ ℂ) = c • monomial α 1 := by
      rw [smul_monomial, smul_eq_mul, mul_one]
    rw [pair_monomial, this, map_smul, smul_eq_mul, coeff_sum]
    congr 1
    simp only [coeff_monomial, Finset.sum_ite_eq', Set.Finite.mem_toFinset, Set.mem_setOf_eq]
    split_ifs with hd
    · exact mul_div_cancel₀ _ (wt_ne_zero α)
    · rw [h α (not_le.1 hd), mul_zero]
  | add P P' h h' => simp only [map_add, LinearMap.add_apply, h, h']

open Classical in
theorem subst_eq_lin {ι : Type} [Fintype ι] {m n : ℕ} (a : ι → Matrix (Fin n) (Fin n) ℂ)
    (b : ι → Matrix (Fin m) (Fin m) ℂ) :
    subst a b = lin fun v w => if v.1 = w.1 then b v.1 w.2.1 v.2.1 * a v.1 v.2.2 w.2.2 else 0 := by
  unfold subst lin
  congr 1
  funext v
  rw [Fintype.sum_prod_type, Finset.sum_eq_single v.1, Fintype.sum_prod_type]
  · simp
  · intro τ _ hτ
    simp [Ne.symm hτ]
  · simp

theorem exists_pair (ι : Type) [Fintype ι] (m n : ℕ) :
    ∃ B : Pol ι m n →ₗ[ℂ] Pol ι m n →ₗ[ℂ] ℂ, (∀ Q, (∀ P, B P Q = 0) → Q = 0) ∧
      (∀ a b P Q, B (subst a b P) Q =
        B P (subst (fun τ => (a τ).transpose) (fun τ => (b τ).transpose) Q)) ∧
      ∀ (ℓ : Pol ι m n →ₗ[ℂ] ℂ) (d : ℕ),
        (∀ α : ι × Fin m × Fin n →₀ ℕ, d < α.degree → ℓ (MvPolynomial.monomial α 1) = 0) →
          ∃ Q, ∀ P, B P Q = ℓ P := by
  refine ⟨pair, pair_nondeg, fun a b P Q => ?_, pair_rep⟩
  rw [subst_eq_lin, subst_eq_lin, pair_lin]
  congr 3
  funext v w
  by_cases h : v.1 = w.1
  · simp [h]
  · simp [h, Ne.symm h]

end GlobalTheory.DefLift.BilFischer

end
