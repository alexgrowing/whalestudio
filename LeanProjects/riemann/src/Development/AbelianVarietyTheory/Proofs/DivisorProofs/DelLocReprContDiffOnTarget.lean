import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsTypeIsRealConst
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClosedFormsMulClosed
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DelAtEqSumDOne
open Set Matrix MeasureTheory Filter Topology
open GlobalTheory.HermFrame
open scoped ComplexOrder ContDiff ComplexConjugate

noncomputable section

namespace GlobalTheory.CxForm.HolAtlas

open GlobalTheory.GoodMetric (coordVec)

theorem del_loc_repr_contDiffOn : ∀ {M : Type} [TopologicalSpace M] {n : ℕ} (A : GlobalTheory.CxForm.HolAtlas M n) (α : A.Fld), A.IsForm α → ∀ (i : A.ι) (S : Finset (Fin (n + n))), ContDiffOn ℝ ∞ (fun v => (GlobalTheory.CxForm.bas n).repr (A.loc (A.del α) i v) S) (A.e i).target := by
  intro M _ n A α hα i S
  have key : ∀ v ∈ (A.e i).target, (GlobalTheory.CxForm.bas n).repr (A.loc (A.del α) i v) S =
      ∑ a, ∑ T, GlobalTheory.del (fun x => (GlobalTheory.CxForm.bas n).repr (A.loc α i x) T) v (coordVec a) *
        (GlobalTheory.CxForm.bas n).repr (GlobalTheory.CxForm.dz a * GlobalTheory.CxForm.bas n T) S := by
    intro v hv
    have h1 : A.loc (A.del α) i v = GlobalTheory.CxForm.delAt (A.loc α i) v := by
      rw [GlobalTheory.CxForm.HolAtlas.loc, dif_pos hv]
      simp only [GlobalTheory.CxForm.HolAtlas.del, GlobalTheory.CxForm.HolAtlas.Pt.crd, GlobalTheory.CxForm.HolAtlas.Pt.ch, GlobalTheory.CxForm.HolAtlas.Pt.pt, (A.e i).right_inv hv]
    rw [h1, GlobalTheory.CxForm.delAt]
    simp only [GlobalTheory.CxForm.coefwise, Finset.mul_sum, mul_smul_comm, map_sum, map_smul,
      Finsupp.finset_sum_apply, Finsupp.smul_apply, smul_eq_mul]
  refine ContDiffOn.congr ?_ key
  have ho := (A.e i).open_target
  refine ContDiffOn.sum fun a _ => ContDiffOn.sum fun T _ => ContDiffOn.mul ?_ contDiffOn_const
  have hf := hα.smooth i T
  have hd := hf.fderiv_of_isOpen ho (m := ∞) (by simp)
  have h1 : ContDiffOn ℝ ∞ (fun v => fderiv ℝ (fun x => (GlobalTheory.CxForm.bas n).repr (A.loc α i x) T) v (coordVec a))
      (A.e i).target := hd.clm_apply contDiffOn_const
  have h2 : ContDiffOn ℝ ∞ (fun v => fderiv ℝ (fun x => (GlobalTheory.CxForm.bas n).repr (A.loc α i x) T) v
      (Complex.I • coordVec a)) (A.e i).target := hd.clm_apply contDiffOn_const
  refine ((h1.sub (h2.const_smul Complex.I)).const_smul (1 / 2 : ℂ)).congr fun v _ => ?_
  rfl

end GlobalTheory.CxForm.HolAtlas
