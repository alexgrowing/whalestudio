import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExpoConjOfIsCsd
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.QminorSwapAdjacent

open NumberField IsDedekindDomain MeasureTheory Formalism.L2.Host GlobalTheory.CuspRep Formalism.REAL

namespace GlobalTheory.CapAdInv

section Algebra

variable {A : Type} [Ring A] [Algebra ℂ A]

theorem qdet_ad {n : ℕ} (E : Fin n → Fin n → A) (hE : GlRel E) (P Q : Matrix (Fin n) (Fin n) ℂ)
    (hQP : Q * P = 1) (u : ℂ) :
    qdet (fun a b => ∑ c, ∑ d, (P c a * Q b d) • E c d) u = qdet E u := by
  first
  | exact @_root_.GlobalTheory.QuantumMinorAdjacentSwap.qdet_conj
  | exact _root_.GlobalTheory.QuantumMinorAdjacentSwap.qdet_conj
  | (apply _root_.GlobalTheory.QuantumMinorAdjacentSwap.qdet_conj <;> assumption)
  | (intros; apply _root_.GlobalTheory.QuantumMinorAdjacentSwap.qdet_conj <;> assumption)
  | (intros; apply @_root_.GlobalTheory.QuantumMinorAdjacentSwap.qdet_conj <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.QuantumMinorAdjacentSwap.qdet_conj ..)

theorem qdet_semiconj {n : ℕ} (E E' : Fin n → Fin n → A) (R : A) (h : ∀ a b, R * E a b = E' a b * R) (u : ℂ) :
    R * qdet E u = qdet E' u * R := by
  have hp : ∀ {t : ℕ} (x y : Fin t → A), (∀ k, R * x k = y k * R) →
      R * (List.ofFn x).prod = (List.ofFn y).prod * R := by
    intro t
    induction t with
    | zero => simp
    | succ t ih =>
      intro x y h
      simp only [List.ofFn_succ, List.prod_cons]
      rw [← mul_assoc, h, mul_assoc, ih _ _ (fun k => h k.succ), mul_assoc]
  simp only [qdet, qminor, Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [← mul_assoc, ← (Int.cast_commute _ R).eq, mul_assoc, mul_assoc, hp]
  intro k
  simp only [Tm, mul_add, add_mul, h]
  split_ifs
  · rw [Algebra.commutes]
  · simp

end Algebra

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ}

theorem rt_lie (y : GL (Fin a) (Cinf E)) (X : Matrix (Fin a) (Fin a) (Cinf E)) :
    rt E a (infGL E a y) * lie E a (toL X) = lie E a (toL (y.val * X * (y⁻¹).val)) * rt E a (infGL E a y) := by
  refine LinearMap.ext fun φ => Subtype.ext <| funext fun g => ?_
  change fderiv ℝ (chart φ.1 (g * infGL E a y)) (oneL E a) (toL X) =
    fderiv ℝ (chart (fun x => φ.1 (x * infGL E a y)) g) (oneL E a) (toL (y.val * X * (y⁻¹).val))
  have hd : DifferentiableAt ℝ (chart φ.1 g) (toL y.val) :=
    (contDiffAt_chart φ.2 g (val_mem_invSet y)).differentiableAt (by simp)
  have e1 : lmul (toL y.val) (oneL E a) = toL y.val := mul_one y.val
  have e2 : rmul (toL y.val) (oneL E a) = toL y.val := one_mul y.val
  rw [chart_mul, chart_rt_inf, fderiv_comp _ (by rw [e1]; exact hd) (lmul (toL y.val)).differentiableAt,
    fderiv_comp _ (by rw [e2]; exact hd) (rmul (toL y.val)).differentiableAt, e1, e2,
    ContinuousLinearMap.fderiv, ContinuousLinearMap.fderiv]
  exact congrArg (fun Z => fderiv ℝ (chart φ.1 g) (toL y.val) (toL Z)) (Units.inv_mul_cancel_right (y.val * X) y).symm

omit [NumberField E] [IsTotallyComplex E] in

theorem mul_atEmb (τ : E →+* ℂ) (x : Cinf E) (z : ℂ) : x * atEmb τ z = atEmb τ (coord τ x * z) := by
  classical
  funext w
  unfold atEmb coord
  by_cases hw : w = InfinitePlace.mk τ
  · subst hw; split_ifs <;> simp
  · simp [Pi.single_eq_of_ne hw]

theorem rt_lieS (y : GL (Fin a) (Cinf E)) (τ : E →+* ℂ) (i j : Fin a) (z : ℂ) :
    rt E a (infGL E a y) * lieS E a i j (atEmb τ z) =
      (∑ k, ∑ l, lieS E a k l (atEmb τ (coord τ (y.val k i) * coord τ ((y⁻¹).val j l) * z))) *
        rt E a (infGL E a y) := by
  rw [lieS_apply, rt_lie]
  congr 1
  have e : y.val * Matrix.single i j (atEmb τ z) * (y⁻¹).val =
      ∑ k, ∑ l, Matrix.single k l (atEmb τ (coord τ (y.val k i) * coord τ ((y⁻¹).val j l) * z)) := by
    rw [Matrix.matrix_eq_sum_single (y.val * Matrix.single i j (atEmb τ z) * (y⁻¹).val)]
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
    congr 1
    rw [← map_mul, ← mul_atEmb]
    simp [Matrix.mul_apply, Matrix.single_apply, ite_and, mul_right_comm]
  rw [e]
  let L : Matrix (Fin a) (Fin a) (Cinf E) →ₗ[ℝ] Module.End ℂ (Sm E a) := lie E a
  have key : ∀ f : Fin a → Fin a → Matrix (Fin a) (Fin a) (Cinf E), L (∑ k, ∑ l, f k l) = ∑ k, ∑ l, L (f k l) :=
    fun f => by simp only [map_sum]
  exact key _

theorem rt_Eop (y : GL (Fin a) (Cinf E)) (τ : E →+* ℂ) (i j : Fin a) :
    rt E a (infGL E a y) * Eop τ i j =
      (∑ k, ∑ l, (coord τ (y.val k i) * coord τ ((y⁻¹).val j l)) • Eop τ k l) * rt E a (infGL E a y) := by
  rw [Eop, mul_smul_comm, mul_sub, mul_smul_comm, rt_lieS, rt_lieS, ← smul_mul_assoc, ← sub_mul, ← smul_mul_assoc]
  congr 1
  simp only [Finset.smul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
  generalize coord τ (y.val k i) * coord τ ((y⁻¹).val j l) = c
  have hL : ∀ w : ℂ, lieS E a k l (atEmb τ w) =
      (w.re : ℂ) • lieS E a k l (atEmb τ 1) + (w.im : ℂ) • lieS E a k l (atEmb τ Complex.I) := fun w => by
    rw [atEmb_eq τ w, map_add, map_smul, map_smul]
    rfl
  rw [hL (c * 1), hL (c * Complex.I), Eop]
  conv_rhs => rw [← Complex.re_add_im c]
  simp only [mul_one, Complex.mul_I_re, Complex.mul_I_im, Complex.ofReal_neg]
  match_scalars
  · ring
  · linear_combination ((c.im : ℂ) / 2) * Complex.I_mul_I

theorem cap_commute_rt_infGL : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (τ : E →+* ℂ) (u : ℂ)
    (y : GL (Fin a) (Cinf E)), Commute (cap (a := a) τ u) (rt E a (infGL E a y)) := by
  intro E _ _ _ a τ u y
  have h := qdet_semiconj _ _ _ (rt_Eop y τ) (u + ((a : ℂ) - 1) / 2)
  have hQP : ((y⁻¹).val.map (coord τ)) * (y.val.map (coord τ)) = 1 := by
    rw [← Matrix.map_mul, Units.inv_mul]; simp
  have h2 := qdet_ad _ (glRel_Eop τ) _ _ hQP (u + ((a : ℂ) - 1) / 2)
  simp only [Matrix.map_apply] at h2
  rw [h2] at h
  exact h.symm

end GlobalTheory.CapAdInv
