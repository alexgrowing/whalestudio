import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DbarEqZeroOfHolomorphic
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WedgeContrSelfApply
open Matrix GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe GlobalTheory.TorsionForm GlobalTheory.TorsionForm.FlatAcyc
open scoped Real ContDiff

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.TorsionForm.FlatAcyc

theorem dbarF_dbarF {g : ℕ} (f : (Fin g → ℂ) → Ext (0 + 0 + g))
    (hf1 : ∀ v, Differentiable ℝ (fun z => d01 f z v))
    (hsym : ∀ z v w, d01 (fun z' => d01 f z' v) z w = d01 (fun z' => d01 f z' w) z v)
    (z : Fin g → ℂ) : dbarF (dbarF f) z = 0 := by
  set A : Fin g → Fin g → Ext (0 + 0 + g) :=
    fun d a => d01 (fun z' => d01 f z' (ev a)) z (ev d) with hA
  have hdiff : ∀ a, DifferentiableAt ℝ (fun z' => wedge (dzb 0 a) (d01 f z' (ev a))) z := fun a =>
    ((wedgeR (dzb 0 a)).differentiable.comp (hf1 (ev a))).differentiableAt
  have h1 : ∀ d, d01 (fun z' => ∑ a, wedge (dzb 0 a) (d01 f z' (ev a))) z (ev d) =
      ∑ a, wedge (dzb 0 a) (A d a) := by
    intro d
    rw [d01_sum Finset.univ (fun a _ => hdiff a)]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    exact dbar_wedge_comm (dzb 0 a) ((hf1 (ev a)) z) (ev d)
  have hX : dbarF (dbarF f) z = ∑ d, ∑ a, wedge (dzb 0 d) (wedge (dzb 0 a) (A d a)) := by
    unfold dbarF
    refine Finset.sum_congr rfl (fun d _ => ?_)
    rw [h1 d]
    have := map_sum (wedgeR (dzb 0 d)) (fun a => wedge (dzb 0 a) (A d a)) Finset.univ
    simpa only [wedgeR_apply] using this
  have hneg : ∑ d, ∑ a, wedge (dzb 0 d) (wedge (dzb 0 a) (A d a)) =
      -∑ d, ∑ a, wedge (dzb 0 d) (wedge (dzb 0 a) (A d a)) := by
    conv_lhs =>
      arg 2; ext d; arg 2; ext a
      rw [wedge_wedge, show A d a = A a d from hsym z (ev a) (ev d)]
    rw [Finset.sum_comm]
    simp only [Finset.sum_neg_distrib]
  rw [hX]
  exact self_eq_neg.mp hneg

end GlobalTheory.TorsionForm.FlatAcyc
