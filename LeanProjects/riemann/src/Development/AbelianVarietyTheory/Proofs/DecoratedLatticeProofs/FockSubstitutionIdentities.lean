import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.EvalAtOneExtremalMul
open MvPolynomial Formalism.BasicNotions Formalism.L2.Forms Formalism.L2.Ker GlobalTheory.KJInf MeasureTheory
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.KJInf

variable {ι : Type} [Fintype ι] {a b : ℕ}

theorem sum_three_fintype_reverse {α β γ M : Type} [Fintype α] [Fintype β] [Fintype γ] [AddCommMonoid M] (f : α → β → γ → M) :
    ∑ x, ∑ y, ∑ z, f x y z = ∑ z, ∑ y, ∑ x, f x y z := by
  calc ∑ x, ∑ y, ∑ z, f x y z = ∑ x, ∑ z, ∑ y, f x y z := Finset.sum_congr rfl fun _ _ => Finset.sum_comm
    _ = ∑ z, ∑ x, ∑ y, f x y z := Finset.sum_comm
    _ = ∑ z, ∑ y, ∑ x, f x y z := Finset.sum_congr rfl fun _ _ => Finset.sum_comm

theorem sum_four_fintype_permute {α β γ δ M : Type} [Fintype α] [Fintype β] [Fintype γ] [Fintype δ] [AddCommMonoid M] (f : α → β → γ → δ → M) :
    ∑ k, ∑ j, ∑ i, ∑ l, f k j i l = ∑ i, ∑ l, ∑ j, ∑ k, f k j i l := by
  calc ∑ k, ∑ j, ∑ i, ∑ l, f k j i l = ∑ i, ∑ j, ∑ k, ∑ l, f k j i l := sum_three_fintype_reverse _
    _ = ∑ i, ∑ j, ∑ l, ∑ k, f k j i l := Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_comm
    _ = ∑ i, ∑ l, ∑ j, ∑ k, f k j i l := Finset.sum_congr rfl fun _ _ => Finset.sum_comm

theorem mvZ_subY_comp (hab : a ≤ b) (g : ι → Matrix (Fin a) (Fin a) ℂ) (h y' : ι → Matrix (Fin b) (Fin b) ℂ) :
    (mvZ g h).comp (subY hab y') = (subY hab (fun τ => h τ * y' τ)).comp (lft g) := by
  apply MvPolynomial.algHom_ext
  intro v
  rw [AlgHom.comp_apply, AlgHom.comp_apply, subY, lft, aeval_X, aeval_X, map_sum, map_sum]
  simp only [map_mul, mvZ, subY, aeval_X, algHom_C, algebraMap_eq, map_sum]
  simp only [Matrix.mul_apply, map_sum, map_mul, Finset.mul_sum, Finset.sum_mul]
  rw [sum_three_fintype_reverse]
  refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => ?_
  ring

theorem mvZ_mvZ_comp (g g' : ι → Matrix (Fin a) (Fin a) ℂ) (h h' : ι → Matrix (Fin b) (Fin b) ℂ) :
    (mvZ g h).comp (mvZ g' h') = mvZ (fun τ => g' τ * g τ) (fun τ => h τ * h' τ) := by
  apply MvPolynomial.algHom_ext
  intro v
  rw [AlgHom.comp_apply]
  simp only [map_mul, mvZ, aeval_X, algHom_C, algebraMap_eq, map_sum]
  simp only [Matrix.mul_apply, map_sum, map_mul, Finset.mul_sum, Finset.sum_mul]
  rw [sum_four_fintype_permute]
  refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => ?_
  ring

theorem lft_lft_comp (g g' : ι → Matrix (Fin a) (Fin a) ℂ) :
    (lft g).comp (lft g') = lft (fun τ => g' τ * g τ) := by
  apply MvPolynomial.algHom_ext
  intro v
  rw [AlgHom.comp_apply]
  simp only [map_mul, lft, aeval_X, algHom_C, algebraMap_eq, map_sum]
  simp only [Matrix.mul_apply, map_sum, map_mul, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => ?_
  ring

theorem mvZ_one : mvZ (ι := ι) (a := a) (b := b) (fun _ => 1) (fun _ => 1) = AlgHom.id ℂ _ := by
  apply MvPolynomial.algHom_ext
  intro v
  simp [mvZ, Matrix.one_apply, apply_ite C, ite_mul, Finset.sum_ite_eq, Finset.sum_ite_eq']

theorem lft_one : lft (ι := ι) (a := a) (fun _ => 1) = AlgHom.id ℂ _ := by
  apply MvPolynomial.algHom_ext
  intro v
  simp [lft, Matrix.one_apply]

def scaleFP (t : ι → ℂ) : FP ι a b →ₐ[ℂ] FP ι a b :=
  aeval fun v => C (t v.1) * X v

theorem subY_smul (hab : a ≤ b) (t : ι → ℂ) (y' : ι → Matrix (Fin b) (Fin b) ℂ) :
    subY hab (fun τ => t τ • y' τ) = (scaleFP t).comp (subY hab y') := by
  apply MvPolynomial.algHom_ext
  intro v
  simp only [subY, scaleFP, AlgHom.comp_apply, aeval_X, map_sum, map_mul, algHom_C,
    Matrix.smul_apply, smul_eq_mul, C_mul, algebraMap_eq]
  refine Finset.sum_congr rfl fun β _ => ?_
  ring

theorem scaleVariables_monomial (t : ι → ℂ) (m : (ι × Fin b × Fin a) →₀ ℕ) :
    scaleFP t (monomial m (1 : ℂ)) = (m.prod fun k n => t k.1 ^ n) • monomial m (1 : ℂ) := by
  rw [scaleFP, aeval_monomial, map_one, one_mul, ← C_mul', ← prod_X_pow_eq_monomial]
  simp only [Finsupp.prod, mul_pow, Finset.prod_mul_distrib, map_prod, map_pow]

theorem jetL_monomial_one (c : ι → ℂ) (G : VCx ι a b → ℂ) (m : (ι × Fin b × Fin a) →₀ ℕ) :
    jetL c G (monomial m (1 : ℂ)) = jetC c G m := by
  have e : (monomial m (1 : ℂ) : FP ι a b) = basisMonomials (ι × Fin b × Fin a) ℂ m := by
    rw [coe_basisMonomials]
  rw [e, jetL, Module.Basis.constr_basis]

theorem jetL_comp_scale (c t : ι → ℂ) (G : VCx ι a b → ℂ) :
    (jetL c G).comp (scaleFP (a := a) (b := b) t).toLinearMap = jetL (fun τ => c τ * t τ) G := by
  refine (basisMonomials (ι × Fin b × Fin a) ℂ).ext fun m => ?_
  simp only [LinearMap.comp_apply, AlgHom.toLinearMap_apply, coe_basisMonomials]
  rw [scaleVariables_monomial, map_smul, jetL_monomial_one, jetL_monomial_one, smul_eq_mul, jetC, jetC, ← mul_assoc]
  congr 1
  simp only [Finsupp.prod, mul_pow, Finset.prod_mul_distrib]
  ring

theorem evalAt_frDet (y : ι → Matrix (Fin a) (Fin a) ℂ) (τ : ι) :
    evalAt y (frDet ℂ a τ : PY ι a) = (y τ).det := by
  rw [evalAt, frDet, RingHom.map_det]
  congr 1
  ext α s
  simp

theorem evalAt_mul_prod (y : ι → Matrix (Fin a) (Fin a) ℂ) (F : PY ι a) :
    evalAt y (F * ∏ τ, (frDet ℂ a τ : PY ι a)) = evalAt y F * ∏ τ, (y τ).det := by
  unfold evalAt
  rw [map_mul, map_prod]
  congr 1
  exact Finset.prod_congr rfl fun τ _ => evalAt_frDet y τ

theorem frDet_prod_ne_zero : (∏ τ, (frDet ℂ a τ : PY ι a)) ≠ 0 := by
  intro h
  have h1 : (1 : PY ι a) * ∏ τ, (frDet ℂ a τ : PY ι a) = 0 := by rw [one_mul, h]
  have h2 := congrArg (evalAt (fun _ : ι => (1 : Matrix (Fin a) (Fin a) ℂ))) h1
  rw [evalAt_mul_prod] at h2
  simp [evalAt] at h2

theorem eq_zero_of_invertible (F : PY ι a) (hF : ∀ y, IsInv y → evalAt y F = 0) : F = 0 := by
  have h0 : F * ∏ τ, (frDet ℂ a τ : PY ι a) = 0 := by
    apply MvPolynomial.funext
    intro x
    have key : eval x (F * ∏ τ, (frDet ℂ a τ : PY ι a)) =
        evalAt (fun τ => Matrix.of fun α s => x (τ, α, s)) (F * ∏ τ, (frDet ℂ a τ : PY ι a)) := rfl
    rw [map_zero, key, evalAt_mul_prod]
    by_cases hI : IsInv (fun τ => Matrix.of fun α s => x (τ, α, s))
    · rw [hF _ hI, zero_mul]
    · simp only [IsInv, not_forall] at hI
      obtain ⟨τ, hτ⟩ := hI
      rw [Finset.prod_eq_zero (Finset.mem_univ τ) (by simpa using hτ), mul_zero]
  exact (mul_eq_zero.mp h0).resolve_right frDet_prod_ne_zero

theorem evalAt_lft_eq (g y : ι → Matrix (Fin a) (Fin a) ℂ) (F : PY ι a) :
    evalAt y (lft g F) = evalAt (fun τ => g τ * y τ) F := by
  simp only [evalAt, lft]
  induction F using MvPolynomial.induction_on with
  | C r => simp
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p v hp =>
    simp only [map_mul, hp, aeval_X, eval_X, map_sum, eval_C, Matrix.mul_apply]

theorem substIdentities : ∀ (ι : Type) [Fintype ι] (a b : ℕ) (hab : a ≤ b), (∀ (g : ι → Matrix (Fin a) (Fin a) ℂ) (h y' : ι → Matrix (Fin b) (Fin b) ℂ) (F : PY ι a), mvZ g h (subY hab y' F) = subY hab (fun τ => h τ * y' τ) (lft g F)) ∧ (∀ (g g' : ι → Matrix (Fin a) (Fin a) ℂ) (h h' : ι → Matrix (Fin b) (Fin b) ℂ) (P : FP ι a b), mvZ g h (mvZ g' h' P) = mvZ (fun τ => g' τ * g τ) (fun τ => h τ * h' τ) P) ∧ (∀ P : FP ι a b, mvZ (fun _ => 1) (fun _ => 1) P = P) ∧ (∀ (g g' : ι → Matrix (Fin a) (Fin a) ℂ) (F : PY ι a), lft g (lft g' F) = lft (fun τ => g' τ * g τ) F) ∧ (∀ F : PY ι a, lft (fun _ => 1) F = F) ∧ (∀ (g y : ι → Matrix (Fin a) (Fin a) ℂ) (F : PY ι a), evalAt y (lft g F) = evalAt (fun τ => g τ * y τ) F) ∧ (∀ F : PY ι a, (∀ y, IsInv y → evalAt y F = 0) → F = 0) ∧ ∀ (c t : ι → ℂ) (G : VCx ι a b → ℂ) (y' : ι → Matrix (Fin b) (Fin b) ℂ) (F : PY ι a), jetL c G (subY hab (fun τ => t τ • y' τ) F) = jetL (fun τ => c τ * t τ) G (subY hab y' F) := by
  intro ι _ a b hab
  refine ⟨fun g h y' F => ?_, fun g g' h h' P => ?_, fun P => ?_, fun g g' F => ?_, fun F => ?_,
    fun g y F => evalAt_lft_eq g y F, fun F hF => eq_zero_of_invertible F hF, fun c t G y' F => ?_⟩
  · have := DFunLike.congr_fun (mvZ_subY_comp hab g h y') F
    simpa only [AlgHom.comp_apply] using this
  · have := DFunLike.congr_fun (mvZ_mvZ_comp g g' h h') P
    simpa only [AlgHom.comp_apply] using this
  · rw [mvZ_one, AlgHom.id_apply]
  · have := DFunLike.congr_fun (lft_lft_comp g g') F
    simpa only [AlgHom.comp_apply] using this
  · rw [lft_one, AlgHom.id_apply]
  · rw [subY_smul, AlgHom.comp_apply, ← AlgHom.toLinearMap_apply, ← LinearMap.comp_apply, jetL_comp_scale]

end GlobalTheory.KJInf
