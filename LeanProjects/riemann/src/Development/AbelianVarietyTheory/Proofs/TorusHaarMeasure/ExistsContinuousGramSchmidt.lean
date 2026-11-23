import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.WeightFunctionOnFrames
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.ProdCastLESucc

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff ENNReal Matrix

namespace GlobalTheory.GramSchmidtCont

open ReciprocityTheory.ChartRestriction.G.FD.FrameDegreeData

theorem continuousOn_inv_apply {T : Type} [TopologicalSpace T] {n : ℕ} {s : Set T}
    {M : T → Matrix (Fin n) (Fin n) ℂ} (hM : Continuous M) (hd : ∀ t ∈ s, (M t).det ≠ 0)
    (i j : Fin n) : ContinuousOn (fun t => (M t)⁻¹ i j) s := by
  have hdet : Continuous fun t => (M t).det := hM.matrix_det
  have hadj : Continuous fun t => (M t).adjugate i j := hM.matrix_adjugate.matrix_elem i j
  simp_rw [Matrix.inv_def, Matrix.smul_apply, smul_eq_mul, Ring.inverse_eq_inv']
  exact (hdet.continuousOn.inv₀ hd).mul hadj.continuousOn

theorem continuousOn_uMat_apply {T : Type} [TopologicalSpace T] {n : ℕ} {s : Set T}
    {M : T → Matrix (Fin n) (Fin n) ℂ} (hM : Continuous M)
    (hd : ∀ t ∈ s, ∀ c : Fin n, (blk (M t) c).det ≠ 0) (j c : Fin n) :
    ContinuousOn (fun t => uMat (M t) j c) s := by
  by_cases hjc : j = c
  · simp only [uMat, Matrix.of_apply, if_pos hjc]
    exact continuousOn_const
  by_cases h : j < c
  · have hB : Continuous fun t => blk (M t) c := by
      unfold blk
      exact hM.matrix_submatrix _ _
    have hinv := fun m k => continuousOn_inv_apply hB (fun t ht => hd t ht c) m k
    simp only [uMat, Matrix.of_apply, if_neg hjc, dif_pos h, Matrix.vecMul, dotProduct, rowc]
    refine ContinuousOn.neg (continuousOn_finsetSum _ fun m _ => ContinuousOn.mul ?_ (hinv m _))
    exact (hM.matrix_elem c _).continuousOn
  · simp only [uMat, Matrix.of_apply, if_neg hjc, dif_neg h]
    exact continuousOn_const

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

omit [NumberField E] [IsCMField E] in

theorem continuous_gram {r : ℕ} (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) :
    Continuous (gram τ G) := by
  refine continuous_matrix fun a b => ?_
  simp only [gram, hermC, col, Matrix.of_apply]
  exact continuous_finsetSum _ fun k _ => continuous_finsetSum _ fun l _ =>
    ((continuous_id.matrix_elem k a).mul continuous_const).mul
      (Complex.continuous_conj.comp (continuous_id.matrix_elem l b))

theorem continuous_mat {r : ℕ} (X : Data E r) (τ : X.Ψ) :
    Continuous (fun x : Frame X.Ψ r => mat x τ) := by
  refine continuous_matrix fun a b => ?_
  simp only [mat, Matrix.of_apply]
  exact (continuous_apply b).comp ((continuous_apply a).comp (continuous_apply τ))

theorem continuousOn_uOf {r : ℕ} (X : Data E r) (τ : X.Ψ) :
    ContinuousOn (fun x : Frame X.Ψ r => uOf X x τ) X.dom := by
  refine continuousOn_pi.2 fun j => continuousOn_pi.2 fun c => ?_
  exact continuousOn_uMat_apply ((continuous_gram τ.1 X.Gm).comp (continuous_mat X τ))
    (fun x hx c => blk_det X hx τ c) j c

theorem continuousOn_dOf {r : ℕ} (X : Data E r) (τ : X.Ψ) (k : Fin r) :
    ContinuousOn (fun x : Frame X.Ψ r => dOf X x τ k) X.dom := by
  show ContinuousOn (fun x => gram τ.1 X.Gm (mat x τ * uOf X x τ) k k) X.dom
  exact ((continuous_id.matrix_elem k k).comp (continuous_gram τ.1 X.Gm)).comp_continuousOn
    ((continuous_mat X τ).continuousOn.mul (continuousOn_uOf X τ))

theorem continuousOn_sOf {r : ℕ} (X : Data E r) (τ : X.Ψ) (k : Fin r) :
    ContinuousOn (fun x : Frame X.Ψ r => sOf X x τ k) X.dom := by
  show ContinuousOn (fun x => (((Real.sqrt |(dOf X x τ k).re|)⁻¹ : ℝ) : ℂ)) X.dom
  refine Complex.continuous_ofReal.comp_continuousOn (ContinuousOn.inv₀ ?_ ?_)
  · exact Real.continuous_sqrt.comp_continuousOn (continuous_abs.comp_continuousOn
      (Complex.continuous_re.comp_continuousOn (continuousOn_dOf X τ k)))
  · intro x hx
    exact (Real.sqrt_pos.2 (abs_re_pos X hx τ k)).ne'

theorem continuousOn_bOf {r : ℕ} (X : Data E r) : ContinuousOn (bOf X) X.dom := by
  refine continuousOn_pi.2 fun τ => ?_
  show ContinuousOn (fun x => (uOf X x τ * Matrix.diagonal (sOf X x τ) : Matrix (Fin r) (Fin r) ℂ)) X.dom
  exact (continuousOn_uOf X τ).mul (continuous_id.matrix_diagonal.comp_continuousOn
    (continuousOn_pi.2 fun k => continuousOn_sOf X τ k))

theorem exists_continuous_gramSchmidt :
    (∀ (r : ℕ) (X : Data E r), ∃ β : Frame X.Ψ r → Frame X.Ψ r, ContinuousOn β X.dom ∧
      ∀ x ∈ X.dom, β x ∈ Bor X.Ψ r ∧ IsOrth X (rmul x (β x))) := by
  intro r X
  exact ⟨bOf X, continuousOn_bOf X, fun x hx => ⟨bOf_mem X hx, ortho_bOf X hx⟩⟩

end GlobalTheory.GramSchmidtCont
