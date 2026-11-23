import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.GROWCountStatement
import ReciprocityTheory.L2DbarEstimates.LeviForms.LogNormSq

namespace ReciprocityTheory.L2DbarEstimates.Y

open MeasureTheory Filter Topology WeightedAtlas
open scoped ContDiff ENNReal Matrix

noncomputable section

namespace ExponentialProfileBounds

variable {n : ℕ}

def wv (n : ℕ) (y : V n) : Fin (n + 1) → ℂ := Fin.cons 1 (fun j => y j)

theorem pos_one_add (y : V n) : 0 < 1 + ‖y‖ ^ 2 := by
  positivity

theorem contDiff_ph (la : ℤ) : ContDiff ℝ ∞ (fun y : V n => (la : ℝ) * Real.log (1 + ‖y‖ ^ 2)) := (contDiff_const.mul ((contDiff_const.add (contDiff_norm_sq ℂ)).log fun y => (pos_one_add y).ne'))

def atlas (n : ℕ) : WeightedAtlas n (V n) Unit ℤ where
  chart _ := OpenPartialHomeomorph.refl (V n)
  pick _ := ()
  mem_pick _ := by simp
  holo_trans _ _ := differentiableOn_id.congr fun _ _ => rfl
  g _ _ _ _ := 1
  holo_g _ _ _ := differentiableOn_const _
  g_ne _ _ _ _ _ _ := one_ne_zero
  g_cocycle _ _ _ _ _ _ _ _ := by simp
  g_add _ _ _ _ _ _ _ := by simp
  ph la _ y := (la : ℝ) * Real.log (1 + ‖y‖ ^ 2)
  smooth_ph la _ := (contDiff_ph la).contDiffOn.congr fun _ _ => rfl
  ph_add la mu _ y _ := by push_cast; ring
  ph_trans _ _ _ _ _ _ := by simp
  kap := 0
  g_kap _ _ y _ _ := by
    rw [show ((OpenPartialHomeomorph.refl (V n)) ∘ (OpenPartialHomeomorph.refl (V n)).symm) = id
      from rfl, fderiv_id]
    exact LinearMap.det_id.symm
  mu := volume
  mu_chart _ A _ _ := by simp

theorem ph_one (y : V n) : (atlas n).ph 1 () y = Real.log (1 + ‖y‖ ^ 2) := by
  simp [atlas]

theorem exp_neg_ph_one (y : V n) : Real.exp (-(atlas n).ph 1 () y) = (1 + ‖y‖ ^ 2)⁻¹ := by
  rw [ph_one, Real.exp_neg, Real.exp_log (pos_one_add y)]

theorem nsq_eq (f : Unit → V n → ℂ) (y : V n) :
    (atlas n).nsq 1 f y = ‖f () y‖ ^ 2 * (1 + ‖y‖ ^ 2)⁻¹ := by
  show ‖f () y‖ ^ 2 * Real.exp (-(atlas n).ph 1 () y) = _
  rw [exp_neg_ph_one]

def wI (n : ℕ) : Fin (n + 1) → Unit → V n → ℂ := fun k _ y => wv n y k

def w0I (n : ℕ) : Unit → V n → ℂ := fun _ _ => 1

def sI (n : ℕ) : Fin n → Unit → V n → ℂ := fun k _ y => y k

theorem hasFDerivAt_coord (m : Fin n) (y : V n) :
    HasFDerivAt (fun v : V n => v m) (EuclideanSpace.proj (𝕜 := ℂ) m) y := (EuclideanSpace.proj (𝕜 := ℂ) m).hasFDerivAt

theorem differentiable_coord (m : Fin n) : Differentiable ℂ (fun v : V n => v m) := fun y => (hasFDerivAt_coord m y).differentiableAt

theorem differentiable_wv (k : Fin (n + 1)) : Differentiable ℂ (fun y : V n => wv n y k) := by
  induction k using Fin.cases with
  | zero => simp only [wv, Fin.cons_zero]; exact differentiable_const _
  | succ j => simp only [wv, Fin.cons_succ]; exact differentiable_coord j

theorem isSecOn_of (la : ℤ) (U : Set (V n)) (f : Unit → V n → ℂ) (hf : Differentiable ℂ (f ())) :
    (atlas n).IsSecOn la U f := ⟨fun i => (hf.comp differentiable_id).differentiableOn, fun i j y _ _ _ => by cases i; cases j; simp [atlas]⟩

theorem norm_sq_eq' (y : V n) : ‖y‖ ^ 2 = ∑ j, ‖y j‖ ^ 2 := by rw [EuclideanSpace.norm_eq, Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)]

theorem sqn_w (y : V n) : (atlas n).sqn 1 (wI n) y = 1 := by
  simp only [WeightedAtlas.sqn, nsq_eq, wI, ← Finset.sum_mul, Fin.sum_univ_succ, wv, Fin.cons_zero,
    Fin.cons_succ, norm_one, one_pow]
  rw [← norm_sq_eq', mul_inv_cancel₀ (pos_one_add y).ne']

theorem euclideanAtlas_sumNormSq_coordSections (y : V n) : (atlas n).sqn 1 (sI n) y = ‖y‖ ^ 2 * (1 + ‖y‖ ^ 2)⁻¹ := by
  simp only [WeightedAtlas.sqn, nsq_eq, sI, ← Finset.sum_mul]
  rw [← norm_sq_eq']

theorem euclideanAtlas_pointwiseNormSq_unitSection (y : V n) : (atlas n).nsq 1 (w0I n) y = (1 + ‖y‖ ^ 2)⁻¹ := by
  rw [nsq_eq]; simp [w0I]

theorem zLoc_eq (i : Unit) : (atlas n).zLoc (w0I n) (sI n) i = id := by
  funext v
  simp [WeightedAtlas.zLoc, w0I, sI, atlas]

theorem det_ne (y : V n) :
    (fderiv ℂ ((atlas n).zLoc (w0I n) (sI n) ((atlas n).pick y))
      ((atlas n).chart ((atlas n).pick y) y)).det ≠ 0 := by
  rw [zLoc_eq, fderiv_id]
  show LinearMap.det (LinearMap.id : V n →ₗ[ℂ] V n) ≠ 0
  rw [LinearMap.det_id]
  exact one_ne_zero

theorem zeroSet_eq : (atlas n).zeroSet (sI n) = {0} := by
  ext y
  simp only [WeightedAtlas.zeroSet, sI, Set.mem_setOf_eq, Set.mem_singleton_iff]
  constructor
  · intro h; ext k; simpa using h k
  · rintro rfl k; simp

theorem contDiff_coord (m : Fin n) : ContDiff ℂ 2 (fun v : V n => v m) := (EuclideanSpace.proj (𝕜 := ℂ) m).contDiff

theorem d0 : (atlas n).D0 1 (wI n) (w0I n) (sI n) where
  sec_w k := isSecOn_of _ _ _ (differentiable_wv k)
  isSection_denom := isSecOn_of _ _ _ (differentiable_const 1)
  sec_s k := isSecOn_of _ _ _ (differentiable_coord k)
  no_common_zero _ := ⟨0, by simp [wI, wv]⟩
  finite_S := by rw [zeroSet_eq]; exact Set.finite_singleton 0
  w0_ne _ _ := one_ne_zero
  coord P _ := det_ne P
  meets y := ⟨0, by rw [zeroSet_eq]; rfl,
    isPreconnected_univ.subset_connectedComponent (Set.mem_univ y) (Set.mem_univ 0)⟩
  family_le_coords U hU hS := by
    have h0 : (0 : V n) ∈ U := hS (by rw [zeroSet_eq]; rfl)
    obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hU 0 h0
    refine ⟨1 + (ε ^ 2)⁻¹, fun y hy => ?_⟩
    have hεy : ε ≤ ‖y‖ := by
      by_contra h
      exact hy (hball (by rw [Metric.mem_ball, dist_zero_right]; exact lt_of_not_ge h))
    rw [sqn_w, euclideanAtlas_sumNormSq_coordSections]
    set t := ‖y‖ ^ 2
    have ht : ε ^ 2 ≤ t := pow_le_pow_left₀ hε.le hεy 2
    have hε2 : 0 < ε ^ 2 := by positivity
    have ht0 : 0 < 1 + t := by positivity
    have key : 1 + t ≤ (1 + (ε ^ 2)⁻¹) * t := by
      have : 1 ≤ (ε ^ 2)⁻¹ * t := (le_inv_mul_iff₀ hε2).2 (by rw [mul_one]; exact ht)
      nlinarith
    calc (1 : ℝ) = (1 + t) * (1 + t)⁻¹ := (mul_inv_cancel₀ ht0.ne').symm
      _ ≤ ((1 + (ε ^ 2)⁻¹) * t) * (1 + t)⁻¹ :=
        mul_le_mul_of_nonneg_right key (inv_nonneg.2 ht0.le)
      _ = _ := by ring
  s_le_w := ⟨1, fun y => by
    rw [sqn_w, euclideanAtlas_sumNormSq_coordSections, mul_one, ← div_eq_mul_inv]
    exact (div_le_one (pos_one_add y)).2 (by linarith)⟩
  denom_le_family := ⟨1, fun y => by
    rw [euclideanAtlas_pointwiseNormSq_unitSection, sqn_w, mul_one]
    exact inv_le_one_of_one_le₀ (by linarith [sq_nonneg ‖y‖])⟩

def gv (n : ℕ) : Fin (n + 1) → V n → ℂ := fun k y => wv n y k

end ExponentialProfileBounds

end

end ReciprocityTheory.L2DbarEstimates.Y
