import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.FundSetMeasStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.MeasInvStatementPf

namespace ReciprocityTheory.ChartRestriction.G.AR.Up.FM

open NumberField Matrix MeasureTheory Topology ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData
  ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.L2DbarEstimates ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.ChartRestriction.G.AR.Up.MI

noncomputable section

attribute [local instance] Classical.propDecidable

theorem cont_inv {α : Type*} [TopologicalSpace α] {n : ℕ} {f : α → Matrix (Fin n) (Fin n) ℂ}
    (hf : Continuous f) (hd : ∀ a, (f a).det ≠ 0) : Continuous fun a => (f a)⁻¹ := by
  have h : (fun a => (f a)⁻¹) = fun a => (f a).det⁻¹ • (f a).adjugate := by
    funext a
    rw [Matrix.inv_def, Ring.inverse_eq_inv']
  rw [h]
  exact (hf.matrix_det.inv₀ hd).smul hf.matrix_adjugate

theorem cont_uMat {α : Type*} [TopologicalSpace α] {n : ℕ} {g : α → Matrix (Fin n) (Fin n) ℂ}
    (hg : Continuous g) (hd : ∀ a c, (blk (g a) c).det ≠ 0) : Continuous fun a => uMat (g a) := by
  refine continuous_pi fun j => continuous_pi fun c => ?_
  simp only [uMat, Matrix.of_apply]
  split_ifs with h1 h2
  · exact continuous_const
  · have hb : Continuous fun a => blk (g a) c := by
      unfold blk
      exact hg.matrix_submatrix _ _
    have hi := cont_inv hb (fun a => hd a c)
    have hr : Continuous fun a => rowc (g a) c := by
      unfold rowc
      exact continuous_pi fun m => (continuous_apply _).comp ((continuous_apply c).comp hg)
    exact ((continuous_apply (⟨j, h2⟩ : Fin c)).comp (hr.matrix_vecMul hi)).neg
  · exact continuous_const

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)

theorem cont_mat (τ : X.Ψ) : Continuous fun y : Frame X.Ψ r => mat y τ := by
  exact continuous_pi fun a => continuous_pi fun b => continuous_coord X τ a b

private theorem continuous_gram_comp {α : Type*} [TopologicalSpace α] (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E)
    {f : α → Matrix (Fin r) (Fin r) ℂ} (hf : Continuous f) :
    Continuous fun a => ReciprocityTheory.ChartRestriction.G.FD.gram τ G (f a) := by
  refine continuous_pi fun i => continuous_pi fun j => ?_
  simp only [ReciprocityTheory.ChartRestriction.G.FD.gram, ReciprocityTheory.ChartRestriction.G.FD.hermC, ReciprocityTheory.ChartRestriction.G.FD.col, Matrix.of_apply]
  refine continuous_finset_sum _ fun a _ => continuous_finset_sum _ fun b _ => ?_
  exact (((continuous_apply i).comp ((continuous_apply a).comp hf)).mul continuous_const).mul
    (Complex.continuous_conj.comp ((continuous_apply j).comp ((continuous_apply b).comp hf)))

theorem cont_gram (τ : X.Ψ) : Continuous fun y : Frame X.Ψ r => gram τ.1 X.Gm (mat y τ) := by
  exact continuous_gram_comp τ.1 X.Gm (cont_mat X τ)

theorem cont_uOf (τ : X.Ψ) : Continuous fun y : X.dom => uOf X y.1 τ := by
  have hg : Continuous fun y : X.dom => gram τ.1 X.Gm (mat y.1 τ) := (cont_gram X τ).comp continuous_subtype_val
  exact cont_uMat hg fun y c => blk_det X y.2 τ c

theorem cont_dOf (τ : X.Ψ) (k : Fin r) : Continuous fun y : X.dom => dOf X y.1 τ k := by
  have hm : Continuous fun y : X.dom => mat y.1 τ * uOf X y.1 τ :=
    ((cont_mat X τ).comp continuous_subtype_val).matrix_mul (cont_uOf X τ)
  exact (continuous_apply k).comp ((continuous_apply k).comp (continuous_gram_comp τ.1 X.Gm hm))

theorem cont_sOf (τ : X.Ψ) (k : Fin r) : Continuous fun y : X.dom => sOf X y.1 τ k := by
  have hd := cont_dOf X τ k
  have hr : Continuous fun y : X.dom => Real.sqrt |(dOf X y.1 τ k).re| :=
    (Complex.continuous_re.comp hd).abs.sqrt
  have hne : ∀ y : X.dom, Real.sqrt |(dOf X y.1 τ k).re| ≠ 0 := fun y =>
    (Real.sqrt_pos.mpr (abs_re_pos X y.2 τ k)).ne'
  exact Complex.continuous_ofReal.comp (hr.inv₀ hne)

theorem cont_bOf (τ : X.Ψ) : Continuous fun y : X.dom => mat (bOf X y.1) τ := by
  exact (cont_uOf X τ).matrix_mul (Continuous.matrix_diagonal (continuous_pi fun k => cont_sOf X τ k))

theorem cont_β0 (τ : X.Ψ) : Continuous fun y : X.dom => β0 X y.1 τ := by
  exact cont_inv (cont_bOf X τ) (fun y => bOf_det X y.2 τ)

theorem β0_bound {C : Set (Frame X.Ψ r)} (hC : IsCompact C) (hCd : C ⊆ X.dom) :
    ∃ R0 : ℝ, ∀ x ∈ C, ∀ τ a b, ‖β0 X x τ a b‖ ≤ R0 := by
  have hcont : ∀ (τ : X.Ψ) (a b : Fin r), ContinuousOn (fun x => ‖β0 X x τ a b‖) C := by
    intro τ a b
    rw [continuousOn_iff_continuous_restrict]
    have h1 : Continuous fun y : X.dom => ‖β0 X y.1 τ a b‖ :=
      ((continuous_apply b).comp ((continuous_apply a).comp (cont_β0 X τ))).norm
    show Continuous fun x : C => ‖β0 X x.1 τ a b‖
    refine (h1.comp (continuous_inclusion hCd)).congr fun x => ?_
    simp only [Function.comp_apply, Set.coe_inclusion]
  choose R hR using fun (τ : X.Ψ) (a b : Fin r) => hC.bddAbove_image (hcont τ a b)
  refine ⟨∑ τ, ∑ a, ∑ b, max (R τ a b) 0, fun x hx τ a b => ?_⟩
  have h1 : ‖β0 X x τ a b‖ ≤ R τ a b := hR τ a b ⟨x, hx, rfl⟩
  calc ‖β0 X x τ a b‖ ≤ max (R τ a b) 0 := h1.trans (le_max_left _ _)
    _ ≤ ∑ b', max (R τ a b') 0 :=
        Finset.single_le_sum (f := fun b' => max (R τ a b') 0) (fun _ _ => le_max_right _ _)
          (Finset.mem_univ b)
    _ ≤ ∑ a', ∑ b', max (R τ a' b') 0 :=
        Finset.single_le_sum (f := fun a' => ∑ b', max (R τ a' b') 0)
          (fun _ _ => Finset.sum_nonneg fun _ _ => le_max_right _ _) (Finset.mem_univ a)
    _ ≤ ∑ τ', ∑ a', ∑ b', max (R τ' a' b') 0 :=
        Finset.single_le_sum (f := fun τ' => ∑ a', ∑ b', max (R τ' a' b') 0)
          (fun _ _ => Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => le_max_right _ _)
          (Finset.mem_univ τ)

end
end ReciprocityTheory.ChartRestriction.G.AR.Up.FM
