import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsTypeIsRealConst
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClosedFormsMulClosed
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DelAtEqSumDOne
open Set Matrix MeasureTheory Filter Topology
open GlobalTheory.HermFrame
open scoped ComplexOrder ContDiff ComplexConjugate

set_option autoImplicit false

noncomputable section

open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory.GoodMetric (coordVec)

namespace GlobalTheory.CxForm.DelForm

theorem coefwise_del_sum_smul {n : ℕ} {ι : Type} [Fintype ι] {v : V n} (g : ι → V n → ℂ) (Q : ι → V n → Alt n)
    (hg : ∀ k, DifferentiableAt ℝ (g k) v) (hQ : ∀ k S, DifferentiableAt ℝ (fun w => (bas n).repr (Q k w) S) v)
    (ξ : V n) :
    coefwise (fun f => del f v ξ) (fun w => ∑ k, g k w • Q k w) =
      ∑ k, (del (g k) v ξ • Q k v + g k v • coefwise (fun f => del f v ξ) (Q k)) := by
  refine (bas n).ext_elem fun S => ?_
  have e : (fun x => (bas n).repr (∑ k, g k x • Q k x) S) = fun x => ∑ k, g k x * (bas n).repr (Q k x) S :=
    funext fun x => by simp only [map_sum, map_smul, Finsupp.finset_sum_apply, Finsupp.smul_apply, smul_eq_mul]
  rw [FormMul.repr_coefwise, e,
    del_sum (A := fun k x => g k x * (bas n).repr (Q k x) S) (fun k _ => (hg k).mul (hQ k S)),
    ContinuousLinearMap.sum_apply, map_sum, Finsupp.finset_sum_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [del_mul (hg k) (hQ k S), map_add, map_smul, map_smul, Finsupp.add_apply, Finsupp.smul_apply, Finsupp.smul_apply,
    FormMul.repr_coefwise, smul_eq_mul, smul_eq_mul, add_comm]

theorem delAt_sum_smul : ∀ {n : ℕ} {ι : Type} [Fintype ι] {v : ReciprocityTheory.L2DbarEstimates.V n} (g : ι → ReciprocityTheory.L2DbarEstimates.V n → ℂ)
    (Q : ι → ReciprocityTheory.L2DbarEstimates.V n → GlobalTheory.CxForm.Alt n), (∀ k, DifferentiableAt ℝ (g k) v) →
    (∀ k S, DifferentiableAt ℝ (fun w => (GlobalTheory.CxForm.bas n).repr (Q k w) S) v) →
    GlobalTheory.CxForm.delAt (fun w => ∑ k, g k w • Q k w) v =
      ∑ k, (GlobalTheory.CxForm.DelForm.dOne (g k) v * Q k v + g k v • GlobalTheory.CxForm.delAt (Q k) v) := by
  intro n ι _ v g Q hg hQ
  simp only [delAt, dOne, coefwise_del_sum_smul g Q hg hQ, Finset.mul_sum, Finset.sum_mul, Finset.smul_sum, mul_add,
    mul_smul_comm, smul_mul_assoc, ← Finset.sum_add_distrib]
  exact Finset.sum_comm

end GlobalTheory.CxForm.DelForm
