import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.ComplexMatrixCalculus.SwapLaws

noncomputable section

open Matrix
open scoped ContDiff

namespace PositivityTheory.RgBcC.Cxe

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

set_option linter.unusedSectionVars false

variable {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

theorem contDiff_entry (i : ι) (j : κ) : ContDiff ℝ ∞ (fun x : Matrix ι κ ℂ => x i j) := by
  have h1 : ContDiff ℝ ∞ (fun x : Matrix ι κ ℂ => x i) := contDiff_pi.mp contDiff_id i
  exact contDiff_pi.mp h1 j

theorem contDiffOn_matrix_iff {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {s : Set E}
    (f : E → Matrix ι κ ℂ) : ContDiffOn ℝ ∞ f s ↔ ∀ i j, ContDiffOn ℝ ∞ (fun x => f x i j) s := by
  constructor
  · intro h i j
    exact contDiffOn_pi.mp (contDiffOn_pi.mp h i) j
  · intro h
    exact contDiffOn_pi.mpr fun i => contDiffOn_pi.mpr fun j => h i j

theorem contDiff_matrix_iff {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : E → Matrix ι κ ℂ) : ContDiff ℝ ∞ f ↔ ∀ i j, ContDiff ℝ ∞ (fun x => f x i j) := by
  constructor
  · intro h i j
    exact contDiff_pi.mp (contDiff_pi.mp h i) j
  · intro h
    exact contDiff_pi.mpr fun i => contDiff_pi.mpr fun j => h i j

theorem contDiff_det : ContDiff ℝ ∞ (fun x : Matrix ι ι ℂ => x.det) := by
  have e : (fun x : Matrix ι ι ℂ => x.det) =
      fun x => ∑ σ : Equiv.Perm ι, ((Equiv.Perm.sign σ : ℤ) : ℂ) * ∏ i, x (σ i) i := by
    funext x; exact Matrix.det_apply' x
  rw [e]
  refine ContDiff.sum fun σ _ => contDiff_const.mul (contDiff_prod fun i _ => contDiff_entry _ _)

theorem contDiff_adjugate : ContDiff ℝ ∞ (fun x : Matrix ι ι ℂ => x.adjugate) := by
  rw [contDiff_matrix_iff]
  intro i j
  simp only [Matrix.adjugate_apply]
  refine contDiff_det.comp ?_
  rw [contDiff_matrix_iff]
  intro a b
  simp only [Matrix.updateRow_apply]
  split_ifs
  · exact contDiff_const
  · exact contDiff_entry a b

theorem isOpen_det_ne : IsOpen {x : Matrix ι ι ℂ | x.det ≠ 0} :=
  isOpen_ne_fun (contDiff_det (ι := ι)).continuous continuous_const

theorem contDiffOn_inv : ContDiffOn ℝ ∞ (fun x : Matrix ι ι ℂ => x⁻¹) {x | x.det ≠ 0} := by
  have h : ∀ x ∈ {x : Matrix ι ι ℂ | x.det ≠ 0}, x⁻¹ = (x.det)⁻¹ • x.adjugate := fun x _ => by
    rw [Matrix.inv_def, Ring.inverse_eq_inv']
  refine ContDiffOn.congr ?_ h
  rw [contDiffOn_matrix_iff]
  intro i j
  simp only [Matrix.smul_apply, smul_eq_mul]
  exact (contDiff_det.contDiffOn.inv fun x hx => hx).mul (contDiff_matrix_iff _ |>.mp contDiff_adjugate i j).contDiffOn

def entL (a : ι) (k : κ) : Matrix ι κ ℂ →L[ℝ] ℂ :=
  LinearMap.toContinuousLinearMap { toFun := fun x => x a k, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }

@[simp] theorem entL_apply (a : ι) (k : κ) (x : Matrix ι κ ℂ) : entL a k x = x a k := rfl

theorem hasFDerivAt_inv_one :
    HasFDerivAt (fun x : Matrix ι ι ℂ => x⁻¹) (-ContinuousLinearMap.id ℝ (Matrix ι ι ℂ)) 1 := by
  have hd : DifferentiableAt ℝ (fun x : Matrix ι ι ℂ => x⁻¹) 1 :=
    (contDiffOn_inv.contDiffAt (isOpen_det_ne.mem_nhds (by simp))).differentiableAt (by simp)
  have hL := hd.hasFDerivAt
  set L := fderiv ℝ (fun x : Matrix ι ι ℂ => x⁻¹) 1 with hLdef
  suffices hLe : L = -ContinuousLinearMap.id ℝ (Matrix ι ι ℂ) by rwa [hLe] at hL
  have hev : ∀ a b : ι, (fun x : Matrix ι ι ℂ => (x * x⁻¹) a b) =ᶠ[nhds 1] fun _ => (1 : Matrix ι ι ℂ) a b := by
    intro a b
    filter_upwards [isOpen_det_ne.mem_nhds (show (1 : Matrix ι ι ℂ).det ≠ 0 by simp)] with x hx
    rw [Matrix.mul_nonsing_inv x (isUnit_iff_ne_zero.mpr hx)]
  have hent : ∀ a b : ι, HasFDerivAt (fun x : Matrix ι ι ℂ => (x * x⁻¹) a b)
      (∑ k, ((1 : Matrix ι ι ℂ) a k • (entL k b).comp L + ((1 : Matrix ι ι ℂ)⁻¹ k b) • entL a k)) 1 := by
    intro a b
    simp only [Matrix.mul_apply]
    refine HasFDerivAt.fun_sum (u := Finset.univ) (A := fun k (x : Matrix ι ι ℂ) => x a k * x⁻¹ k b) fun k _ => ?_
    have h1 : HasFDerivAt (fun x : Matrix ι ι ℂ => x a k) (entL a k) 1 := (entL a k).hasFDerivAt
    have h2 : HasFDerivAt (fun x : Matrix ι ι ℂ => x⁻¹ k b) ((entL k b).comp L) 1 := (entL k b).hasFDerivAt.comp 1 hL
    exact h1.mul h2
  ext X i j
  have h0 := (hent i j).unique ((hasFDerivAt_const ((1 : Matrix ι ι ℂ) i j) (1 : Matrix ι ι ℂ)).congr_of_eventuallyEq (hev i j))
  have h0X := congrArg (fun T : Matrix ι ι ℂ →L[ℝ] ℂ => T X) h0
  simp only [ContinuousLinearMap.coe_sum', Finset.sum_apply, ContinuousLinearMap.add_apply, ContinuousLinearMap.coe_smul',
    Pi.smul_apply, ContinuousLinearMap.coe_comp', Function.comp_apply, entL_apply, smul_eq_mul, inv_one,
    ContinuousLinearMap.zero_apply, Finset.sum_add_distrib] at h0X
  simp only [Matrix.one_apply, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true, mul_ite, mul_one,
    mul_zero, Finset.sum_ite_eq'] at h0X
  simp only [ContinuousLinearMap.neg_apply, ContinuousLinearMap.id_apply, Matrix.neg_apply]
  linear_combination h0X

end PositivityTheory.RgBcC.Cxe
