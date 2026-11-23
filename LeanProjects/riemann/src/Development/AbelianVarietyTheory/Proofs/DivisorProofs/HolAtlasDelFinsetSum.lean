import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsTypeIsRealConst
open Set Matrix MeasureTheory
open GlobalTheory.HermFrame
open scoped ComplexOrder

namespace GlobalTheory.CxForm.HolAtlas

theorem del_finset_sum {M : Type} [TopologicalSpace M] {n : ℕ} (A : GlobalTheory.CxForm.HolAtlas M n) {N : ℕ}
    (α : Fin N → A.Fld) (hα : ∀ j, A.IsForm (α j)) : A.del (∑ j, α j) = ∑ j, A.del (α j) := by
  funext x
  have hloc : ∀ w, A.loc (∑ j, α j) x.1.1 w = ∑ j, A.loc (α j) x.1.1 w := by
    intro w
    by_cases hw : w ∈ (A.e x.1.1).target
    · simp only [GlobalTheory.CxForm.HolAtlas.loc, hw, dif_pos]
      exact Finset.sum_apply _ _ _
    · simp [GlobalTheory.CxForm.HolAtlas.loc, hw]
  have hx : x.crd ∈ (A.e x.1.1).target := x.ch.map_source x.2
  have hdiff : ∀ j S, DifferentiableAt ℝ (fun w => (GlobalTheory.CxForm.bas n).repr (A.loc (α j) x.1.1 w) S) x.crd :=
    fun j S => (((hα j).smooth x.1.1 S).differentiableOn (by simp)).differentiableAt
      ((A.e x.1.1).open_target.mem_nhds hx)
  have key : ∀ S u, GlobalTheory.del (fun w => (GlobalTheory.CxForm.bas n).repr (A.loc (∑ j, α j) x.1.1 w) S) x.crd u =
      ∑ j, GlobalTheory.del (fun w => (GlobalTheory.CxForm.bas n).repr (A.loc (α j) x.1.1 w) S) x.crd u := by
    intro S u
    have e : (fun w => (GlobalTheory.CxForm.bas n).repr (A.loc (∑ j, α j) x.1.1 w) S) =
        fun w => ∑ j ∈ Finset.univ, (GlobalTheory.CxForm.bas n).repr (A.loc (α j) x.1.1 w) S := by
      funext w; rw [hloc, map_sum, Finsupp.finset_sum_apply]
    rw [e, GlobalTheory.del_sum (fun j _ => hdiff j S), ContinuousLinearMap.sum_apply]
  rw [Finset.sum_apply]
  simp only [GlobalTheory.CxForm.HolAtlas.del, GlobalTheory.CxForm.delAt, GlobalTheory.CxForm.coefwise, key, Finset.sum_smul, Finset.mul_sum]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => ?_
  exact Finset.sum_comm

end GlobalTheory.CxForm.HolAtlas
