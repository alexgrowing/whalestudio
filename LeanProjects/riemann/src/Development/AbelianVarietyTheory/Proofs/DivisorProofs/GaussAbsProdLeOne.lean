import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.JoinCastSucc
import ReciprocityTheory.SemistableReduction.TorusL2CauchyInequality

set_option autoImplicit false

open NumberField MvPolynomial

namespace GlobalTheory.GaussSubst

variable {E : Type} [Field E] [NumberField E] (v : FinitePlace E)

theorem gaussAbs_nonneg {τ : Type} (f : MvPolynomial τ E) : 0 ≤ ReciprocityTheory.MultiplicativeHeights.gaussAbs v f := by
  unfold ReciprocityTheory.MultiplicativeHeights.gaussAbs
  exact NNReal.coe_nonneg _

theorem gaussAbs_mul_le {τ : Type} (f g : MvPolynomial τ E) :
    ReciprocityTheory.MultiplicativeHeights.gaussAbs v (f * g) ≤ ReciprocityTheory.MultiplicativeHeights.gaussAbs v f * ReciprocityTheory.MultiplicativeHeights.gaussAbs v g := by
  classical
  have hf := gaussAbs_nonneg v f
  have hg := gaussAbs_nonneg v g
  refine ReciprocityTheory.MultiplicativeHeights.gauss_abs_le_of_coeff_le v _ (mul_nonneg hf hg) fun u => ?_
  rw [MvPolynomial.coeff_mul]
  refine ReciprocityTheory.MultiplicativeHeights.finite_place_sum_le v _ _ (mul_nonneg hf hg) fun x _ => ?_
  rw [map_mul]
  exact mul_le_mul (ReciprocityTheory.MultiplicativeHeights.coeff_le_gauss_abs v f _) (ReciprocityTheory.MultiplicativeHeights.coeff_le_gauss_abs v g _)
    (apply_nonneg v _) hf

theorem gaussAbs_one_le {τ : Type} : ReciprocityTheory.MultiplicativeHeights.gaussAbs v (1 : MvPolynomial τ E) ≤ 1 := by
  classical
  refine ReciprocityTheory.MultiplicativeHeights.gauss_abs_le_of_coeff_le v _ zero_le_one fun s => ?_
  rw [MvPolynomial.coeff_one]
  split_ifs <;> simp

theorem gaussAbs_pow_le_one {τ : Type} (f : MvPolynomial τ E)
    (hf : ReciprocityTheory.MultiplicativeHeights.gaussAbs v f ≤ 1) (n : ℕ) : ReciprocityTheory.MultiplicativeHeights.gaussAbs v (f ^ n) ≤ 1 := by
  induction n with
  | zero => simpa using gaussAbs_one_le v
  | succ n ih =>
    rw [pow_succ]
    exact (gaussAbs_mul_le v _ _).trans
      (mul_le_one₀ ih (gaussAbs_nonneg v f) hf)

theorem gaussAbs_prod_le_one {τ ι : Type} (t : Finset ι) (F : ι → MvPolynomial τ E)
    (hF : ∀ i ∈ t, ReciprocityTheory.MultiplicativeHeights.gaussAbs v (F i) ≤ 1) :
    ReciprocityTheory.MultiplicativeHeights.gaussAbs v (∏ i ∈ t, F i) ≤ 1 := by
  classical
  induction t using Finset.induction_on with
  | empty => simpa using gaussAbs_one_le v
  | insert a t ha ih =>
    rw [Finset.prod_insert ha]
    exact (gaussAbs_mul_le v _ _).trans
      (mul_le_one₀ (hF a (Finset.mem_insert_self a t)) (gaussAbs_nonneg v _)
        (ih fun i hi => hF i (Finset.mem_insert_of_mem hi)))

theorem gaussAbs_C_mul_le {τ : Type} (a : E) (f : MvPolynomial τ E)
    (hf : ReciprocityTheory.MultiplicativeHeights.gaussAbs v f ≤ 1) : ReciprocityTheory.MultiplicativeHeights.gaussAbs v (C a * f) ≤ v a := by
  refine ReciprocityTheory.MultiplicativeHeights.gauss_abs_le_of_coeff_le v _ (apply_nonneg v _) fun s => ?_
  rw [MvPolynomial.coeff_C_mul, map_mul]
  exact mul_le_of_le_one_right (apply_nonneg v _)
    ((ReciprocityTheory.MultiplicativeHeights.coeff_le_gauss_abs v f s).trans hf)

theorem gaussAbs_aeval_le : ∀ (E : Type) [Field E] [NumberField E] (v : FinitePlace E) (σ τ : Type)
    (φ : σ → MvPolynomial τ E) (g : MvPolynomial σ E),
    (∀ i, ReciprocityTheory.MultiplicativeHeights.gaussAbs v (φ i) ≤ 1) →
      ReciprocityTheory.MultiplicativeHeights.gaussAbs v (aeval φ g) ≤ ReciprocityTheory.MultiplicativeHeights.gaussAbs v g := by
  intro E _ _ v σ τ φ g h
  have h0 := gaussAbs_nonneg v g
  refine ReciprocityTheory.MultiplicativeHeights.gauss_abs_le_of_coeff_le v _ h0 fun t => ?_
  rw [aeval_def, eval₂_eq, coeff_sum]
  refine ReciprocityTheory.MultiplicativeHeights.finite_place_sum_le v _ _ h0 fun s _ => ?_
  have hprod : ReciprocityTheory.MultiplicativeHeights.gaussAbs v (∏ i ∈ s.support, φ i ^ s i) ≤ 1 :=
    gaussAbs_prod_le_one v _ _ fun i _ => gaussAbs_pow_le_one v _ (h i) _
  have hC := gaussAbs_C_mul_le v (coeff s g) _ hprod
  rw [MvPolynomial.algebraMap_eq]
  exact (ReciprocityTheory.MultiplicativeHeights.coeff_le_gauss_abs v _ t).trans
    (hC.trans (ReciprocityTheory.MultiplicativeHeights.coeff_le_gauss_abs v g s))

end GlobalTheory.GaussSubst
