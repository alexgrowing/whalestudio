import Mathlib
import Development.AbelianVarietyTheory.Definitions.UpperBounds.FreeBallIffOfDimXEqZero
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.ContinuousInvLeadingBlockEntry
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.WeightFunctionOnFrames
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.CuspidalExponentialDecay
import ReciprocityTheory.L2DbarEstimates.LeviForms.EventuallyDifferentiableAtOfContDiffAt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.ExhaustFStatementPfE
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.OntoStatementPfB

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff ENNReal Matrix

namespace GlobalTheory.PotentialTransfer

open Filter Matrix GlobalTheory.SharpGradient GlobalTheory.Up
open scoped ComplexOrder ComplexConjugate

section Matrices

variable {n p : ℕ}

def topT (h : p ≤ n) (g : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin p) (Fin p) ℂ :=
  (g.submatrix (Fin.castLE h) (Fin.castLE h))ᵀ

def lowT (h : p ≤ n) (g : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin p) (Fin n) ℂ :=
  Matrix.of fun a k => if (k : ℕ) < p then 0 else g k (Fin.castLE h a)

noncomputable def graphT (h : p ≤ n) (g : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin p) (Fin n) ℂ :=
  (topT h g)⁻¹ * lowT h g

theorem leading_gram (h : p ≤ n) (g : Matrix (Fin n) (Fin n) ℂ) :
    (gᵀ * (Matrix.diagonal fun a : Fin n => ((sgn p (a : ℕ) : ℝ) : ℂ)) *
      g.map (starRingEnd ℂ)).submatrix (Fin.castLE h) (Fin.castLE h) =
      topT h g * (topT h g)ᴴ - lowT h g * (lowT h g)ᴴ := by
  ext a b
  have e2 : (topT h g * (topT h g)ᴴ) a b = ∑ k : Fin n, if (k : ℕ) < p then
      g k (Fin.castLE h a) * starRingEnd ℂ (g k (Fin.castLE h b)) else 0 := by
    rw [Matrix.mul_apply]
    refine Fintype.sum_of_injective (Fin.castLE h) (Fin.castLE_injective h) _ _ (fun k hk => ?_)
      (fun k => ?_)
    · rw [if_neg]
      intro hlt
      exact hk ⟨⟨k, hlt⟩, Fin.ext rfl⟩
    · simp [topT, Matrix.conjTranspose_apply]
  rw [Matrix.sub_apply, e2, Matrix.submatrix_apply, Matrix.mul_apply, Matrix.mul_apply,
    ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Matrix.mul_diagonal]
  by_cases hk : (k : ℕ) < p
  · simp [lowT, sgn, hk, Matrix.conjTranspose_apply]
  · simp [lowT, sgn, hk, Matrix.conjTranspose_apply]

theorem one_sub_graph (h : p ≤ n) (g : Matrix (Fin n) (Fin n) ℂ) (hd : (topT h g).det ≠ 0) :
    1 - graphT h g * (graphT h g)ᴴ =
      (topT h g)⁻¹ * (topT h g * (topT h g)ᴴ - lowT h g * (lowT h g)ᴴ) * ((topT h g)⁻¹)ᴴ := by
  have hu : IsUnit (topT h g).det := isUnit_iff_ne_zero.2 hd
  have h1 : (topT h g)⁻¹ * topT h g = 1 := Matrix.nonsing_inv_mul _ hu
  have h2 : (topT h g)ᴴ * ((topT h g)⁻¹)ᴴ = 1 := by
    rw [← Matrix.conjTranspose_mul, h1, Matrix.conjTranspose_one]
  rw [Matrix.mul_sub, Matrix.sub_mul, ← Matrix.mul_assoc, h1, Matrix.one_mul, h2, graphT,
    Matrix.conjTranspose_mul]
  simp only [Matrix.mul_assoc]

theorem graph_posDef (h : p ≤ n) (g : Matrix (Fin n) (Fin n) ℂ) (hd : (topT h g).det ≠ 0)
    (hP : (topT h g * (topT h g)ᴴ - lowT h g * (lowT h g)ᴴ).PosDef) :
    (1 - graphT h g * (graphT h g)ᴴ).PosDef ∧
      (1 - graphT h g * (graphT h g)ᴴ).det.re =
        ‖(topT h g * (topT h g)ᴴ - lowT h g * (lowT h g)ᴴ).det‖ / ‖(topT h g).det‖ ^ 2 := by
  have hu : IsUnit (topT h g)⁻¹ := by
    rw [Matrix.isUnit_nonsing_inv_iff, Matrix.isUnit_iff_isUnit_det]
    exact isUnit_iff_ne_zero.2 hd
  have hpd : (1 - graphT h g * (graphT h g)ᴴ).PosDef := by
    rw [one_sub_graph h g hd]
    exact (Matrix.IsUnit.posDef_star_right_conjugate_iff hu).2 hP
  refine ⟨hpd, ?_⟩
  rw [← ExF.norm_of_pos hpd.det_pos, one_sub_graph h g hd, Matrix.det_mul, Matrix.det_mul,
    Matrix.det_conjTranspose, Matrix.det_nonsing_inv, Ring.inverse_eq_inv', norm_mul, norm_mul,
    norm_star, norm_inv]
  have : ‖(topT h g).det‖ ≠ 0 := norm_ne_zero_iff.2 hd
  field_simp

theorem contDiffAt_graph {m : ℕ} (h : p ≤ n) {g : V m → Matrix (Fin n) (Fin n) ℂ}
    (hg : ∀ a b, ContDiff ℂ ∞ fun y => g y a b) {z : V m} (hd : (topT h (g z)).det ≠ 0)
    (a : Fin p) (k : Fin n) : ContDiffAt ℂ ∞ (fun y => graphT h (g y) a k) z := by
  have ht : ∀ i j, ContDiff ℂ ∞ fun y => topT h (g y) i j := fun i j => hg _ _
  have e : (fun y => graphT h (g y) a k) = fun y => ∑ b, (((topT h (g y)).det)⁻¹ *
      ((topT h (g y)).updateRow b (Pi.single a 1)).det) * lowT h (g y) b k := by
    funext y
    simp [graphT, Matrix.inv_def, Matrix.mul_apply, Matrix.adjugate_apply, Ring.inverse_eq_inv']
  rw [e]
  refine ContDiffAt.sum fun b _ => ContDiffAt.mul (ContDiffAt.mul ?_ ?_) ?_
  · exact (ExhD.contDiff_det_of ht).contDiffAt.inv hd
  · refine (ExhD.contDiff_det_of fun i j => ?_).contDiffAt
    simp only [Matrix.updateRow_apply]
    split_ifs
    · exact contDiff_const
    · exact ht _ _
  · simp only [lowT, Matrix.of_apply]
    split_ifs
    · exact contDiffAt_const
    · exact (hg _ _).contDiffAt

end Matrices

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} {X : Data E r}
  {x1 x2 x : Frame X.Ψ r}

theorem det_topT_ne_zero (h2 : IsOrth X x2) (hx : x ∈ X.dom) (τ : X.Ψ) :
    (topT X.p0_le ((mat x2 τ)⁻¹ * mat x τ)).det ≠ 0 := by
  rw [topT, Matrix.det_transpose]
  exact lminor_inv_mul_ne_zero h2 hx τ

theorem gramPos_eq (h2 : IsOrth X x2) (x : Frame X.Ψ r) (τ : X.Ψ) :
    X.gramPos x τ = topT X.p0_le ((mat x2 τ)⁻¹ * mat x τ) * (topT X.p0_le ((mat x2 τ)⁻¹ * mat x τ))ᴴ -
      lowT X.p0_le ((mat x2 τ)⁻¹ * mat x τ) * (lowT X.p0_le ((mat x2 τ)⁻¹ * mat x τ))ᴴ := by
  have hu : IsUnit (mat x2 τ).det := isUnit_iff_ne_zero.mpr (LUPf.orthogonalFrame_det_ne_zero X x2 h2 τ)
  rw [← leading_gram, ← h2 τ, ← FrameDegreeData.gram_mul, Matrix.mul_nonsing_inv_cancel_left _ _ hu]
  rfl

theorem graph_posDef_of_mem (h2 : IsOrth X x2) (hx : x ∈ X.dom) (τ : X.Ψ) :
    (1 - graphT X.p0_le ((mat x2 τ)⁻¹ * mat x τ) *
      (graphT X.p0_le ((mat x2 τ)⁻¹ * mat x τ))ᴴ).PosDef :=
  (graph_posDef _ _ (det_topT_ne_zero h2 hx τ) (gramPos_eq h2 x τ ▸ X.gramPos_posDef hx τ)).1

theorem rhX_eq_sum_graph (h2 : IsOrth X x2) (hx : x ∈ X.dom) :
    rhX X x2 x = ∑ τ, -Real.log (1 - graphT X.p0_le ((mat x2 τ)⁻¹ * mat x τ) *
      (graphT X.p0_le ((mat x2 τ)⁻¹ * mat x τ))ᴴ).det.re := by
  rw [rhX_eq_sum_log h2 hx]
  refine Finset.sum_congr rfl fun τ _ => ?_
  rw [(graph_posDef _ _ (det_topT_ne_zero h2 hx τ) (gramPos_eq h2 x τ ▸ X.gramPos_posDef hx τ)).2,
    ← gramPos_eq h2 x τ, topT, Matrix.det_transpose]
  rfl

theorem contDiff_inv_mul_cpt (x1 x2 : Frame X.Ψ r) (τ : X.Ψ) (a b : Fin r) :
    ContDiff ℂ ∞ fun y : V (nd X) => ((mat x2 τ)⁻¹ * mat (cpt X x1 y) τ) a b := by
  simp only [Matrix.mul_apply]
  exact ContDiff.sum fun c _ => contDiff_const.mul (OntoB.cd_cpt_entry X x1 τ c b)

noncomputable def minorProd (X : Data E r) (x1 x2 : Frame X.Ψ r) (y : V (nd X)) : ℂ :=
  ∏ τ, lminor ((mat x2 τ)⁻¹ * mat (cpt X x1 y) τ) ⟨X.p0, Nat.lt_succ_of_le X.p0_le⟩

theorem contDiff_minorProd (x1 x2 : Frame X.Ψ r) : ContDiff ℂ ∞ (minorProd X x1 x2) :=
  contDiff_prod fun τ _ => ExhD.contDiff_det_of fun _ _ => contDiff_inv_mul_cpt x1 x2 τ _ _

theorem minorProd_ne_zero (h2 : IsOrth X x2) {y : V (nd X)} (hy : y ∈ OmF X x1) :
    minorProd X x1 x2 y ≠ 0 :=
  Finset.prod_ne_zero_iff.2 fun τ _ => lminor_inv_mul_ne_zero h2 hy τ

theorem rhX_cpt_eq_add (h2 : IsOrth X x2) {y : V (nd X)} (hy : y ∈ OmF X x1) :
    rhX X x2 (cpt X x1 y) = rhF X x1 y + Real.log (Complex.normSq (minorProd X x1 x2 y)) := by
  rw [rhX_eq_sum h2 hy, minorProd, map_prod, Real.log_prod fun τ _ =>
    (Complex.normSq_pos.2 (lminor_inv_mul_ne_zero h2 hy τ)).ne']
  simp only [Complex.normSq_eq_norm_sq]
  rfl

theorem contDiffAt_log_minorProd (h2 : IsOrth X x2) {z : V (nd X)} (hz : z ∈ OmF X x1) :
    ContDiffAt ℝ ∞ (fun y => Real.log (Complex.normSq (minorProd X x1 x2 y))) z := by
  have hn : ContDiff ℝ ∞ fun y : V (nd X) => Complex.normSq (minorProd X x1 x2 y) := by
    simp only [Complex.normSq_eq_norm_sq]
    exact (contDiff_norm_sq ℝ).comp ((contDiff_minorProd x1 x2).restrict_scalars ℝ)
  exact (Real.contDiffAt_log.2 (Complex.normSq_pos.2 (minorProd_ne_zero h2 hz)).ne').comp z
    hn.contDiffAt

theorem rhX_cpt_eventuallyEq (h2 : IsOrth X x2) {z : V (nd X)} (hz : z ∈ OmF X x1) :
    (fun y => rhX X x2 (cpt X x1 y)) =ᶠ[𝓝 z]
      fun y => rhF X x1 y + Real.log (Complex.normSq (minorProd X x1 x2 y)) := by
  filter_upwards [(OntoB.isOpen_OmF X x1).mem_nhds hz] with y hy
  exact rhX_cpt_eq_add h2 hy

theorem contDiffAt_rhX_cpt (h2 : IsOrth X x2) {z : V (nd X)} (hz : z ∈ OmF X x1) :
    ContDiffAt ℝ ∞ (fun y => rhX X x2 (cpt X x1 y)) z :=
  ((OntoB.rhF_contDiffAt hz).add (contDiffAt_log_minorProd h2 hz)).congr_of_eventuallyEq
    (rhX_cpt_eventuallyEq h2 hz)

theorem leviO_rhX (h2 : IsOrth X x2) {z : V (nd X)} (hz : z ∈ OmF X x1) (ξ : Fin (nd X) → ℂ) :
    leviO X x1 (rhX X x2) z ξ = leviRh X x1 z ξ := by
  have e : (fun y => ((rhX X x2 (cpt X x1 y) : ℝ) : ℂ)) =ᶠ[𝓝 z]
      fun y => ((rhF X x1 y + Real.log (Complex.normSq (minorProd X x1 x2 y)) : ℝ) : ℂ) := by
    filter_upwards [rhX_cpt_eventuallyEq h2 hz] with y hy
    rw [hy]
  unfold leviO leviM leviRh
  rw [ReciprocityTheory.L2DbarEstimates.leviV_congr e ξ,
    ReciprocityTheory.L2DbarEstimates.Y.LocalMaximumSecondDerivative.leviV_ofReal_add
      ((OntoB.rhF_contDiffAt hz).of_le ExhE.two_le_infty)
      ((contDiffAt_log_minorProd h2 hz).of_le ExhE.two_le_infty) ξ,
    ExF.levi_logNormSq_zero _ (contDiff_minorProd x1 x2) z (minorProd_ne_zero h2 hz) ξ, add_zero]

theorem sharpAt_rhX_cpt (h2 : IsOrth X x2) {z : V (nd X)} (hz : z ∈ OmF X x1)
    (ξ : Fin (nd X) → ℂ) : SharpAt (fun y => rhX X x2 (cpt X x1 y)) z ξ := by
  choose U hU he using fun τ => exists_unitary_rows (graph_posDef_of_mem h2 hz τ)
  have hS : SharpAt (fun y => ∑ τ, ∑ a, -Real.log (1 - ∑ b, Complex.normSq
      (((U τ)ᴴ * graphT X.p0_le ((mat x2 τ)⁻¹ * mat (cpt X x1 y) τ)) a b))) z ξ := by
    refine sharpAt_sum' fun τ => sharpAt_sum fun a => ?_
    refine sharpAt_ball
      (g := fun b y => ((U τ)ᴴ * graphT X.p0_le ((mat x2 τ)⁻¹ * mat (cpt X x1 y) τ)) a b) ξ
      (fun b => ?_) (row_lt_one _ (hU τ) (graph_posDef_of_mem h2 hz τ) a)
    simp only [Matrix.mul_apply]
    exact (ContDiffAt.sum fun c _ => contDiffAt_const.mul
      (contDiffAt_graph X.p0_le (contDiff_inv_mul_cpt x1 x2 τ) (det_topT_ne_zero h2 hz τ) c b)).of_le
      ExhE.two_le_infty
  refine hS.of_minorant ((contDiffAt_rhX_cpt h2 hz).of_le ExhE.two_le_infty) ?_ ?_
  · filter_upwards [(OntoB.isOpen_OmF X x1).mem_nhds hz] with y hy
    rw [rhX_eq_sum_graph h2 hy]
    exact Finset.sum_le_sum fun τ _ => rows_le_neg_log_det _ (hU τ) (graph_posDef_of_mem h2 hy τ)
  · rw [rhX_eq_sum_graph h2 hz]
    exact Finset.sum_congr rfl fun τ _ => he τ

theorem potential_transfer : RhTr (E := E) := by
  intro r X x1 x2 _ h2
  refine ⟨fun z hz => (contDiffAt_rhX_cpt h2 hz).contDiffWithinAt, fun z hz =>
    ⟨rhX_nonneg h2 hz, fun ξ => ⟨leviO_rhX h2 hz ξ, ?_⟩⟩⟩
  rw [← leviO_rhX h2 hz ξ]
  exact (sharpAt_rhX_cpt h2 hz ξ).2.2.2

end GlobalTheory.PotentialTransfer
