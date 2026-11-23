import Formalism.PeriodIntegrals.FlagGramNonneg

noncomputable section

open Matrix PI.FlagGramNonneg
open scoped ComplexOrder

namespace PI.UnitaryGroupMassFormula.FlagGramNonneg

theorem cT_star_eq {m n : Type} (M : Matrix m n ℂ) : cT (starRingEnd ℂ) M = Mᴴ := by
  ext i j
  simp [cT, Matrix.conjTranspose_apply]

theorem form_mulVec {m n : Type} [Fintype m] [Fintype n] (A : Matrix m n ℂ) (B : Matrix m m ℂ)
    (u : n → ℂ) :
    star (A *ᵥ u) ⬝ᵥ (B *ᵥ (A *ᵥ u)) = star u ⬝ᵥ ((Aᴴ * B * A) *ᵥ u) := by
  rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec,
    Matrix.mul_assoc]

theorem form_reindex {n m : Type} [Fintype n] [Fintype m] (e : n ≃ m) (J : Matrix n n ℂ)
    (x : n → ℂ) :
    star (fun i => x (e.symm i)) ⬝ᵥ ((J.reindex e e) *ᵥ (fun i => x (e.symm i))) =
      star x ⬝ᵥ (J *ᵥ x) := by
  have h : (J.reindex e e) *ᵥ (fun i => x (e.symm i)) = fun i => (J *ᵥ x) (e.symm i) := by
    rw [Matrix.reindex_apply, Matrix.submatrix_mulVec_equiv]
    funext i
    simp [Function.comp_def]
  rw [h]
  simp only [dotProduct, Pi.star_apply]
  exact Equiv.sum_comp e.symm (fun i => star (x i) * (J *ᵥ x) i)

theorem Jpq_mulVec_of {p q : ℕ} (u : Fin p ⊕ Fin q → ℂ) (hu : ∀ j, u (Sum.inr j) = 0) :
    Jpq p q *ᵥ u = u := by
  have h0 : (u ∘ Sum.inr) = 0 := funext hu
  rw [Jpq, Matrix.fromBlocks_mulVec, h0]
  funext i
  cases i <;> simp [hu]

theorem hasSignature_exists_nonneg {N p q : ℕ} {ι : Type} [Fintype ι] [DecidableEq ι]
    (J : Matrix (Fin N) (Fin N) ℂ) (hJ : HasSignature J p q) (hq : q < Fintype.card ι)
    (X : Matrix (Fin N) ι ℂ) :
    ∃ c : ι → ℂ, c ≠ 0 ∧ 0 ≤ (star (X *ᵥ c) ⬝ᵥ (J *ᵥ (X *ᵥ c))).re := by
  obtain ⟨e, P, hP⟩ := hJ
  let Q : Matrix (Fin p ⊕ Fin q) (Fin p ⊕ Fin q) ℂ := ((P⁻¹ : GL (Fin p ⊕ Fin q) ℂ) : Matrix _ _ ℂ)
  let Y : Matrix (Fin p ⊕ Fin q) ι ℂ := Q * X.submatrix e.symm id
  let K : Matrix (Fin q) ι ℂ := fun j l => Y (Sum.inr j) l
  have hk : LinearMap.ker (Matrix.mulVecLin K) ≠ ⊥ :=
    LinearMap.ker_ne_bot_of_finrank_lt (by simpa [Module.finrank_fintype_fun_eq_card] using hq)
  obtain ⟨c, hc, hc0⟩ := (Submodule.ne_bot_iff _).mp hk
  refine ⟨c, hc0, ?_⟩
  rw [LinearMap.mem_ker, Matrix.mulVecLin_apply] at hc
  have hy : ∀ j, (Y *ᵥ c) (Sum.inr j) = 0 := fun j => congrFun hc j
  have hx : (fun i => (X *ᵥ c) (e.symm i)) = (P : Matrix _ _ ℂ) *ᵥ (Y *ᵥ c) := by
    rw [Matrix.mulVec_mulVec, ← Matrix.mul_assoc]
    have hPQ : (P : Matrix _ _ ℂ) * Q = 1 := Units.mul_inv P
    rw [hPQ, Matrix.one_mul]
    rfl
  have key : star (X *ᵥ c) ⬝ᵥ (J *ᵥ (X *ᵥ c)) = star (Y *ᵥ c) ⬝ᵥ (Y *ᵥ c) := by
    rw [cT_star_eq] at hP
    rw [← form_reindex e J (X *ᵥ c), hx, form_mulVec, hP, Jpq_mulVec_of _ hy]
  rw [key]
  simp only [dotProduct, Pi.star_apply, Complex.re_sum]
  refine Finset.sum_nonneg fun i _ => ?_
  rw [Complex.star_def, Complex.mul_re, Complex.conj_re, Complex.conj_im]
  nlinarith [mul_self_nonneg ((Y *ᵥ c) i).re, mul_self_nonneg ((Y *ᵥ c) i).im]

end PI.UnitaryGroupMassFormula.FlagGramNonneg
