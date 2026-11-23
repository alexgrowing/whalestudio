import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsTypeIsRealConst
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClosedFormsMulClosed
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DelAtEqSumDOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HolomorphicDelOperatorAtSumSmulLeibnizStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HolomorphicDifferentialOneFormCompHolomorphicStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DifferentiableAtReprPullbackHolomorphicFderivStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HolomorphicDelPullbackFderivFormEqZeroStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DelLocReprContDiffOnTargetStatement

open Set Matrix MeasureTheory Filter Topology
open GlobalTheory.HermFrame
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory.GoodMetric (coordVec)
open scoped ComplexOrder ContDiff ComplexConjugate

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CxForm.DelForm

open GlobalTheory.CxForm

variable {n : ℕ}

theorem delAt_pull_comp {φ : V n → V n} {v : V n} (hφ : ContDiffAt ℂ 2 φ v) {β : V n → Alt n}
    (hβ : ∀ S, DifferentiableAt ℝ (fun u => (bas n).repr (β u) S) (φ v)) :
    delAt (fun w => pull (fderiv ℂ φ w) (β (φ w))) v = pull (fderiv ℂ φ v) (delAt β (φ v)) := by
  have hφ1 : DifferentiableAt ℂ φ v := hφ.differentiableAt two_ne_zero
  have e : (fun w => pull (fderiv ℂ φ w) (β (φ w))) =
      fun w => ∑ T, (bas n).repr (β (φ w)) T • pull (fderiv ℂ φ w) (bas n T) := funext fun w => by
    conv_lhs => rw [← (bas n).sum_repr (β (φ w))]
    simp only [map_sum, map_smul]
  rw [e, GlobalTheory.T.holomorphicDelOperatorAt_sum_smul_leibniz (fun T w => (bas n).repr (β (φ w)) T) (fun T w => pull (fderiv ℂ φ w) (bas n T))
    (fun T => (hβ T).comp v (hφ1.restrictScalars ℝ)) (fun T S => GlobalTheory.T.differentiableAt_repr_pullback_holomorphic_fderiv hφ (bas n T) S)]
  simp only [GlobalTheory.T.holomorphicDel_pullback_fderiv_form_eq_zero hφ, smul_zero, add_zero]
  rw [delAt_eq_sum_dOne β (φ v), map_sum]
  refine Finset.sum_congr rfl fun T _ => ?_
  rw [map_mul, GlobalTheory.T.holomorphicDifferentialOneForm_comp_holomorphic (c := fun u => (bas n).repr (β u) T) (hβ T) hφ1]

variable {M : Type} [TopologicalSpace M] {A : HolAtlas M n}

theorem del_compat {α : A.Fld} (hα : A.IsForm α) (x x' : A.Pt) (h : x.pt = x'.pt) :
    A.del α x = pull (fderiv ℂ (x'.ch ∘ x.ch.symm) x.crd) (A.del α x') := by
  set φ : V n → V n := x'.ch ∘ x.ch.symm with hφdef
  have hW : IsOpen (x.ch.target ∩ x.ch.symm ⁻¹' x'.ch.source) :=
    x.ch.isOpen_inter_preimage_symm x'.ch.open_source
  have hv : x.crd ∈ x.ch.target ∩ x.ch.symm ⁻¹' x'.ch.source :=
    ⟨x.ch.map_source x.2, by simp only [mem_preimage, x.ch.left_inv x.2, h]; exact x'.2⟩
  have hφ : ContDiffAt ℂ 2 φ x.crd := by
    have hd : DifferentiableOn ℂ φ (x.ch.target ∩ x.ch.symm ⁻¹' x'.ch.source) := A.holo x.1.1 x'.1.1
    have hs : ContDiffOn ℂ ∞ φ (x.ch.target ∩ x.ch.symm ⁻¹' x'.ch.source) := (contDiffOn_piLp 2).2 fun c =>
      ReciprocityTheory.L2DbarEstimates.contDiffOn_of_differentiableOn n _ _ hW
        ((EuclideanSpace.proj c : V n →L[ℂ] ℂ).differentiable.comp_differentiableOn hd)
    exact (hs.contDiffAt (hW.mem_nhds hv)).of_le (WithTop.coe_le_coe.2 le_top)
  have hφv : φ x.crd = x'.crd := by simp only [hφdef, Function.comp_apply, x.ch.left_inv x.2, h]
  have hloc : A.loc α x.1.1 =ᶠ[𝓝 x.crd] fun w => pull (fderiv ℂ φ w) (A.loc α x'.1.1 (φ w)) := by
    filter_upwards [hW.mem_nhds hv] with w hw
    let p : A.Pt := ⟨(x.1.1, x.ch.symm w), x.ch.map_target hw.1⟩
    let p' : A.Pt := ⟨(x'.1.1, x.ch.symm w), hw.2⟩
    have hc := hα.compat p p' rfl
    have hp : p.crd = w := x.ch.right_inv hw.1
    rw [HolAtlas.loc, dif_pos hw.1]
    refine hc.trans ?_
    rw [hp, ← A.loc_crd α p']
    rfl
  show delAt (A.loc α x.1.1) x.crd = pull (fderiv ℂ φ x.crd) (delAt (A.loc α x'.1.1) x'.crd)
  rw [delAt_congr hloc, delAt_pull_comp hφ (fun S => hφv ▸ FormMul.differentiableAt_coef hα x' S), hφv]

theorem isForm_del : ∀ {M : Type} [TopologicalSpace M] {n : ℕ} (A : GlobalTheory.CxForm.HolAtlas M n) (α : A.Fld),
    A.IsForm α → A.IsForm (A.del α) :=
  fun A α hα => ⟨GlobalTheory.T.del_loc_repr_contDiffOn_target A α hα, fun x x' h => del_compat hα x x' h⟩

end GlobalTheory.CxForm.DelForm
