import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsTypeIsRealConst

open Set Matrix MeasureTheory
open GlobalTheory.HermFrame
open scoped ComplexOrder

namespace GlobalTheory.CxForm.SmulForm

theorem loc_smul {M : Type} [TopologicalSpace M] {n : ℕ} (A : HolAtlas M n) (c : ℂ) (α : A.Fld) (i : A.ι)
    (v : ReciprocityTheory.L2DbarEstimates.V n) : A.loc (c • α) i v = c • A.loc α i v := by
  unfold HolAtlas.loc
  split_ifs
  · rfl
  · exact (smul_zero c).symm

theorem isForm_smul_and_del_smul {M : Type} [TopologicalSpace M] {n : ℕ} (A : GlobalTheory.CxForm.HolAtlas M n) (c : ℂ)
    (α : A.Fld) (h : A.IsForm α) : A.IsForm (c • α) ∧ A.del (c • α) = c • A.del α := by
  have hc (i : A.ι) (S : Finset (Fin (n + n))) : (fun v => (bas n).repr (A.loc (c • α) i v) S) =
      fun v => c • (bas n).repr (A.loc α i v) S := by
    funext v
    rw [loc_smul, map_smul, Finsupp.smul_apply]
  refine ⟨⟨fun i S => ?_, fun x x' e => ?_⟩, funext fun x => ?_⟩
  · rw [hc]
    exact (h.smooth i S).const_smul c
  · rw [Pi.smul_apply, Pi.smul_apply, map_smul, ← h.compat x x' e]
  · have hd (S : Finset (Fin (n + n))) :
        DifferentiableAt ℝ (fun v => (bas n).repr (A.loc α x.1.1 v) S) x.crd :=
      ((h.smooth x.1.1 S).contDiffAt (x.ch.open_target.mem_nhds (x.ch.map_source x.2))).differentiableAt (by simp)
    rw [Pi.smul_apply, HolAtlas.del, HolAtlas.del, delAt, delAt, Finset.smul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [← mul_smul_comm, coefwise, coefwise, Finset.smul_sum]
    congr 1
    refine Finset.sum_congr rfl fun S _ => ?_
    rw [hc, GlobalTheory.del_const_smul c (hd S), ContinuousLinearMap.smul_apply, smul_assoc]

end GlobalTheory.CxForm.SmulForm
