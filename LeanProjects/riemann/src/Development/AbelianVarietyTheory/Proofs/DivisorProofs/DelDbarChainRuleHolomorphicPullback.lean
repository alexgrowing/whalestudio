import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.LineSCShortExact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContDiffOnCoefficientsComplexFormMulStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DelOperatorAtDbarOperatorAtLinearLocalStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DelOperatorAtDbarOperatorAtLeibnizOfCommuteStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DelOperatorDbarOperatorPullbackConstantFormHolomStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WirtingerDerivsCompHolomorphicPullbackDzStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContDiffOnReprPullbackComplexFormFderivStatement
open GlobalTheory GlobalTheory.CxForm GlobalTheory.GoodMetric
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff ComplexConjugate Topology

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.CxForm.PullChain

variable {n : ℕ}

theorem repr_algebraMap (t : ℂ) (S : Finset (Fin (n + n))) :
    (bas n).repr (algebraMap ℂ (Alt n) t) S = if S = ∅ then t else 0 := by
  rw [Algebra.algebraMap_eq_smul_one, ← bas_empty, map_smul, Module.Basis.repr_self]
  by_cases h : S = ∅ <;> simp [Finsupp.single_apply, h, eq_comm]

theorem delAt_dbarAt_algebraMap (g : V n → ℂ) (v : V n) :
    delAt (fun x => algebraMap ℂ (Alt n) (g x)) v = ∑ a, del g v (coordVec a) • dz a ∧
    dbarAt (fun x => algebraMap ℂ (Alt n) (g x)) v = ∑ a, dbar g v (coordVec a) • dzb a := by
  have h : (fun x => algebraMap ℂ (Alt n) (g x)) = fun x => g x • bas n ∅ := by
    funext x; rw [Algebra.algebraMap_eq_smul_one, bas_empty]
  rw [h]
  constructor
  · unfold delAt
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [coefwise_smul (T := fun f => del f v (coordVec a)) (by simp) g, bas_empty, mul_smul_comm, mul_one]
  · unfold dbarAt
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [coefwise_smul (T := fun f => dbar f v (coordVec a)) (by simp) g, bas_empty, mul_smul_comm, mul_one]

theorem differentiableAt_repr_algebraMap {g : V n → ℂ} {v : V n} (hg : DifferentiableAt ℝ g v)
    (S : Finset (Fin (n + n))) : DifferentiableAt ℝ (fun x => (bas n).repr (algebraMap ℂ (Alt n) (g x)) S) v := by
  simp only [repr_algebraMap]
  split_ifs
  exacts [hg, differentiableAt_const _]

theorem delAt_dbarAt_pull_comp (m n : ℕ) (τ : V m → V n) (U : Set (V m)) (β : V n → Alt n) (v : V m)
    (hU : IsOpen U) (hv : v ∈ U) (hτ : DifferentiableOn ℂ τ U)
    (hβ : ∀ S, DifferentiableAt ℝ (fun y => (bas n).repr (β y) S) (τ v)) :
    delAt (fun x => pull (fderiv ℂ τ x) (β (τ x))) v = pull (fderiv ℂ τ v) (delAt β (τ v)) ∧
    dbarAt (fun x => pull (fderiv ℂ τ x) (β (τ x))) v = pull (fderiv ℂ τ v) (dbarAt β (τ v)) := by
  have hτv : DifferentiableAt ℂ τ v := hτ.differentiableAt (hU.mem_nhds hv)
  have hg : ∀ S, DifferentiableAt ℝ (fun x => (bas n).repr (β (τ x)) S) v :=
    fun S => (hβ S).comp v (hτv.restrictScalars ℝ)
  have hPd : ∀ S T, DifferentiableAt ℝ (fun x => (bas m).repr (pull (fderiv ℂ τ x) (bas n S)) T) v :=
    fun S T => ((GlobalTheory.T.contDiffOn_repr_pullbackComplexForm_fderiv m n τ U (bas n S) hU hτ T).contDiffAt (hU.mem_nhds hv)).differentiableAt (by simp)
  have hA : ∀ S T, DifferentiableAt ℝ
      (fun x => (bas m).repr (algebraMap ℂ (Alt m) ((bas n).repr (β (τ x)) S)) T) v :=
    fun S T => differentiableAt_repr_algebraMap (hg S) T
  have hprod : ∀ S T, DifferentiableAt ℝ (fun x => (bas m).repr
      (algebraMap ℂ (Alt m) ((bas n).repr (β (τ x)) S) * pull (fderiv ℂ τ x) (bas n S)) T) v :=
    fun S => (GlobalTheory.T.contDiffOn_coefficients_complexForm_mul m m (fun x => algebraMap ℂ (Alt m) ((bas n).repr (β (τ x)) S))
      (fun x => pull (fderiv ℂ τ x) (bas n S))).2 v (hA S) (hPd S)
  have hexp : (fun x => pull (fderiv ℂ τ x) (β (τ x))) = fun x => ∑ S,
      algebraMap ℂ (Alt m) ((bas n).repr (β (τ x)) S) * pull (fderiv ℂ τ x) (bas n S) := by
    funext x
    conv_lhs => rw [← (bas n).sum_repr (β (τ x))]
    simp only [map_sum, map_smul, Algebra.smul_def, map_mul, AlgHom.commutes]
  have hsum := (GlobalTheory.T.delOperatorAt_dbarOperatorAt_linear_local m v).2.2.1 (Finset (Fin (n + n))) Finset.univ
    (fun S x => algebraMap ℂ (Alt m) ((bas n).repr (β (τ x)) S) * pull (fderiv ℂ τ x) (bas n S))
    (fun S _ => hprod S)
  have hL := fun S => GlobalTheory.T.delOperatorAt_dbarOperatorAt_leibniz_of_commute m (fun x => algebraMap ℂ (Alt m) ((bas n).repr (β (τ x)) S))
    (fun x => pull (fderiv ℂ τ x) (bas n S)) v (algebraMap ℂ (Alt m) ((bas n).repr (β (τ v)) S)) (hA S) (hPd S)
  have hcl := fun S => GlobalTheory.T.delOperator_dbarOperator_pullback_constantForm_holomorphic m n τ U (bas n S) hU hτ v hv
  have hch := fun S => GlobalTheory.T.wirtingerDerivs_comp_holomorphic_pullback_dz m n τ (fun y => (bas n).repr (β y) S) v hτv (hβ S)
  have hfun := fun S => delAt_dbarAt_algebraMap (fun x => (bas n).repr (β (τ x)) S) v
  rw [hexp]
  constructor
  · rw [hsum.1]
    have key : ∀ S, delAt (fun x => algebraMap ℂ (Alt m) ((bas n).repr (β (τ x)) S) * pull (fderiv ℂ τ x) (bas n S)) v =
        pull (fderiv ℂ τ v) ((∑ a, del (fun y => (bas n).repr (β y) S) (τ v) (coordVec a) • dz a) * bas n S) := by
      intro S
      rw [(hL S).1 (fun a => (Algebra.commutes _ _).symm), (hcl S).1, mul_zero, add_zero, (hfun S).1, (hch S).1,
        map_mul]
    simp only [key, ← map_sum]
    congr 1
    unfold delAt coefwise
    simp only [Finset.mul_sum, Finset.sum_mul, smul_mul_assoc, mul_smul_comm]
    exact Finset.sum_comm
  · rw [hsum.2]
    have key : ∀ S, dbarAt (fun x => algebraMap ℂ (Alt m) ((bas n).repr (β (τ x)) S) * pull (fderiv ℂ τ x) (bas n S)) v =
        pull (fderiv ℂ τ v) ((∑ a, dbar (fun y => (bas n).repr (β y) S) (τ v) (coordVec a) • dzb a) * bas n S) := by
      intro S
      rw [(hL S).2 (fun a => (Algebra.commutes _ _).symm), (hcl S).2, mul_zero, add_zero, (hfun S).2, (hch S).2,
        map_mul]
    simp only [key, ← map_sum]
    congr 1
    unfold dbarAt coefwise
    simp only [Finset.mul_sum, Finset.sum_mul, smul_mul_assoc, mul_smul_comm]
    exact Finset.sum_comm

end GlobalTheory.CxForm.PullChain
