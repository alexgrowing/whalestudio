import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.L2BoundedOnSmooth
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.StSchurW
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.UnitaryGroupStructuralFacts
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.MeasurableBetGm
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.JBeConv
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.JPairs

noncomputable section

open MeasureTheory Matrix
open scoped InnerProductSpace

namespace ReciprocityTheory.ChartRestriction.DS.Mult1

open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2 ReciprocityTheory.ChartRestriction.DS.Mult1.BeEquiv ReciprocityTheory.ChartRestriction.DS.Mult1.Fold

namespace MFix

variable {k r : ℕ}

theorem nR_ge (hk : 1 ≤ k) : (2 : ℝ) ≤ nR k r := by
  unfold nR
  have : (2 : ℕ) ≤ 2 * r + k + 1 := by omega
  exact_mod_cast this

theorem a_nonneg (X : SigData k r) (ha : aM k r ≤ X.a) : 0 ≤ X.a := by
  refine le_trans ?_ ha
  unfold aM nR; positivity

theorem gap (hk : 1 ≤ k) (X : SigData k r) (ha : aM k r ≤ X.a) : AS k r + 1 ≤ min X.a X.a - AG k r - 1 := by
  have hn := nR_ge (r := r) hk
  unfold aM at ha
  unfold AS AG
  rw [min_self]
  have h2 : nR k r ^ 2 * 2 ≤ nR k r ^ 3 := by nlinarith [sq_nonneg (nR k r)]
  have h3 : (4 : ℝ) ≤ nR k r ^ 2 := by nlinarith
  nlinarith

theorem orbit_mem (hGL : GNLower) (X : SigData k r) (ha : aM k r ≤ X.a) {x : Mat k r} (hx : x ∈ GV k r) :
    X.σ x X.w ∈ VflA X X.a := by
  refine ⟨|X.Cw| * gN x⁻¹ ^ X.a, fun g hg => ?_⟩
  rw [mc_sig_left X X.w X.w hg hx]
  have h1 := X.dec (g * x) (gv_mul hg hx)
  have h2 := pow_mul_le hGL hg hx (a_nonneg X ha)
  have h3 : 0 ≤ gN (g * x) ^ (-X.a) := Real.rpow_nonneg (bc_gN_nonneg _) _
  calc ‖mc X X.w X.w (g * x)‖ ≤ X.Cw * gN (g * x) ^ (-X.a) := h1
    _ ≤ |X.Cw| * gN (g * x) ^ (-X.a) := mul_le_mul_of_nonneg_right (le_abs_self _) h3
    _ ≤ |X.Cw| * (gN x⁻¹ ^ X.a * gN g ^ (-X.a)) := mul_le_mul_of_nonneg_left h2 (abs_nonneg _)
    _ = |X.Cw| * gN x⁻¹ ^ X.a * gN g ^ (-X.a) := by ring

variable {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]

def phi (X : SigData k r) (d : ℝ) (W' : Mat k r → Wp) (x : Mat k r) (y : Mt k r) : Wp :=
  ((d : ℂ) * star (mc X X.w X.w (x⁻¹ * Matrix.of y))) • W' (Matrix.of y)

theorem closedG_of (h : UnitaryGroupStructuralFacts) : ClosedG := by
  obtain ⟨⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hCG, -⟩, -⟩ := id h
  exact hCG

theorem phi_integrable (h : UnitaryGroupStructuralFacts) (D : RealPlaceData k r Wp Wp) (X : SigData k r) (d : ℝ) (W' : Mat k r → Wp)
    (hWm : AEStronglyMeasurable (fun y : Mt k r => W' (Matrix.of y)) D.μG) {x : Mat k r} (hx : x ∈ GV k r)
    (hI : Integrable (fun y : Mt k r => gN (x⁻¹ * Matrix.of y) ^ (-X.a) * ‖W' (Matrix.of y)‖) D.μG) :
    Integrable (phi X d W' x) D.μG := by
  have cG : IsClosed {y : Mt k r | (Matrix.of y : Mat k r) ∈ GV k r} := (closedG_of h k r).closed
  have c0 : Continuous (fun y : Mt k r => (x⁻¹ * Matrix.of y : Mat k r)) :=
    Continuous.matrix_mul continuous_const continuous_id
  have c1 : ContinuousOn (fun y : Mt k r => X.σ (x⁻¹ * Matrix.of y) X.w) {y | (Matrix.of y : Mat k r) ∈ GV k r} :=
    (X.rep.2.2 X.w).comp c0.continuousOn (fun y hy => gv_mul (gv_inv hx) hy)
  have c2 : ContinuousOn (fun y : Mt k r => (d : ℂ) * star (mc X X.w X.w (x⁻¹ * Matrix.of y)))
      {y | (Matrix.of y : Mat k r) ∈ GV k r} :=
    continuousOn_const.mul (continuousOn_const.inner c1).star
  have hm := c2.aestronglyMeasurable (μ := D.μG) cG.measurableSet
  have hae : ∀ᵐ y ∂D.μG, y ∈ {y : Mt k r | (Matrix.of y : Mat k r) ∈ GV k r} := ae_mem_of_haarOn D.haarG
  rw [Measure.restrict_eq_self_of_ae_mem hae] at hm
  refine (hI.const_mul (|d| * |X.Cw|)).mono' (hm.smul hWm) ?_
  filter_upwards [ae_mem_of_haarOn D.haarG] with y hy
  have h1 := X.dec _ (gv_mul (gv_inv hx) hy)
  have h3 : 0 ≤ gN (x⁻¹ * Matrix.of y) ^ (-X.a) := Real.rpow_nonneg (bc_gN_nonneg _) _
  have h4 : ‖mc X X.w X.w (x⁻¹ * Matrix.of y)‖ ≤ |X.Cw| * gN (x⁻¹ * Matrix.of y) ^ (-X.a) :=
    h1.trans (mul_le_mul_of_nonneg_right (le_abs_self _) h3)
  unfold phi
  rw [norm_smul, norm_mul, norm_star, Complex.norm_real, Real.norm_eq_abs]
  calc |d| * ‖mc X X.w X.w (x⁻¹ * Matrix.of y)‖ * ‖W' (Matrix.of y)‖
      ≤ |d| * (|X.Cw| * gN (x⁻¹ * Matrix.of y) ^ (-X.a)) * ‖W' (Matrix.of y)‖ := by gcongr
    _ = |d| * |X.Cw| * (gN (x⁻¹ * Matrix.of y) ^ (-X.a) * ‖W' (Matrix.of y)‖) := by ring

theorem phi_Fm (D : RealPlaceData k r Wp Wp) (X : SigData k r) (d : ℝ) (W' : Mat k r → Wp)
    (hW : ∀ h ∈ UWset k r D.z, ∀ m ∈ Nset k r, ∀ x ∈ GV k r, W' (m * h * x) = psiD D m • D.π h (W' x))
    {x : Mat k r} (hx : x ∈ GV k r) {y : Mt k r} (hy : (Matrix.of y : Mat k r) ∈ GV k r) {p : Mt k r × Mt k r}
    (hp : (Matrix.of p.1 : Mat k r) ∈ UWset k r D.z ∧ (Matrix.of p.2 : Mat k r) ∈ Nset k r) :
    phi X d W' x (Fm p y) =
      (d : ℂ) • beInt D X (X.σ x X.w) (X.σ (Matrix.of y) X.w) p (W' (Matrix.of y)) := by
  have e0 : (Matrix.of (Fm p y) : Mat k r) = (Matrix.of p.2 * Matrix.of p.1 : Mat k r)⁻¹ * Matrix.of y := rfl
  unfold phi beInt
  rw [e0]
  obtain ⟨hh, hm⟩ := hp
  generalize (Matrix.of p.1 : Mat k r) = h0 at hh ⊢
  generalize (Matrix.of p.2 : Mat k r) = m at hm ⊢
  generalize (Matrix.of y : Mat k r) = t at hy ⊢
  have hs : m * h0 ∈ GV k r := gv_mul hm.1 hh.1
  have hsx : m * h0 * x ∈ GV k r := gv_mul hs hx
  have e1 : star (mc X X.w X.w (x⁻¹ * ((m * h0)⁻¹ * t))) = mc X (X.σ x X.w) (X.σ t X.w) (m * h0) := by
    rw [mc_sig_left X X.w (X.σ t X.w) hs hx]
    unfold mc
    have e2 : x⁻¹ * ((m * h0)⁻¹ * t) = (m * h0 * x)⁻¹ * t := by
      rw [Matrix.mul_inv_rev (m * h0) x, Matrix.mul_assoc]
    rw [e2, X.rep.1.2 _ (gv_inv hsx) _ hy, ContinuousLinearMap.comp_apply,
      ← inner_sig_move X _ hsx (gv_inv hsx) (gv_mul_inv hsx)]
    exact inner_conj_symm _ _
  have e3 := hW h0 hh m hm ((m * h0)⁻¹ * t) (gv_mul (gv_inv hs) hy)
  rw [← Matrix.mul_assoc, gv_mul_inv hs, Matrix.one_mul] at e3
  have e4 : D.π h0⁻¹ (D.π h0 (W' ((m * h0)⁻¹ * t))) = W' ((m * h0)⁻¹ * t) := by
    have := pi_cancel D (uw_inv hh) (W' ((m * h0)⁻¹ * t))
    rwa [gv_inv_inv hh.1] at this
  have e5 := psiD_star_mul D m
  rw [e1, _root_.smul_apply, e3, ContinuousLinearMap.map_smul, e4, smul_smul, smul_smul]
  congr 1
  linear_combination (-((d : ℂ) * mc X (X.σ x X.w) (X.σ t X.w) (m * h0))) * e5

end MFix

open MFix in
theorem stMFix (h : UnitaryGroupStructuralFacts) : StMFix := by
  intro k r Wp _ _ _ D X hD hsq ha l hl d hd W' hWm hWeq hWint
  have : CompleteSpace Wp := FiniteDimensional.complete ℂ Wp
  have hGL := gnLower_of h
  obtain ⟨b, -, -, hfold⟩ := foldS h D hD
  refine ⟨∫ y : Mt k r, (b y : ℂ) * ((d : ℂ) * ⟪l (X.σ (Matrix.of y) X.w), W' (Matrix.of y)⟫_ℂ) ∂D.μG, fun x hx => ?_⟩
  have hφ := phi_integrable h D X d W' hWm hx (hWint x hx)
  have e1 : ∫ y : Mt k r, ((d : ℂ) * star (mc X X.w X.w (Matrix.of y))) • W' (x * Matrix.of y) ∂D.μG =
      ∫ y, phi X d W' x y ∂D.μG := by
    have hm : AEStronglyMeasurable (phi X d W' x) (D.μG.map (lmulM x)) := by
      rw [D.haarG.left x hx]; exact hφ.aestronglyMeasurable
    have e := integral_map (μ := D.μG) (φ := lmulM x) (measurable_lmul_mt x).aemeasurable hm
    rw [D.haarG.left x hx] at e
    rw [e]
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    have e0 : (Matrix.of (lmulM x y) : Mat k r) = x * Matrix.of y := rfl
    simp only [phi, e0]
    rw [← Matrix.mul_assoc, gv_inv_mul hx, Matrix.one_mul]
  rw [e1, (hfold _ hφ).2, ← integral_smul_const]
  refine integral_congr_ae ?_
  filter_upwards [ae_mem_of_haarOn D.haarG] with y hy
  have hu := orbit_mem hGL X ha hx
  have hv := orbit_mem hGL X ha hy
  have hI := stBeConv h k r Wp D X hD hsq _ (gap D.k_pos X ha) _ _
    (stPairs h k r Wp D X hD hsq d hd X.a X.a _ hu _ hv)
  have e2 : ∫ p, phi X d W' x (Fm p y) ∂(D.μW.prod D.μN) =
      (d : ℂ) • beOp D X (X.σ x X.w) (X.σ (Matrix.of y) X.w) (W' (Matrix.of y)) := by
    unfold beOp
    rw [ContinuousLinearMap.integral_apply hI, ← integral_smul]
    refine integral_congr_ae ?_
    filter_upwards [ae_mem_S D] with p hp
    exact phi_Fm D X d W' hWeq hx hy hp
  rw [e2, hl.2 _ hu _ hv]
  simp only [rk1, ContinuousLinearMap.smulRight_apply, innerSL_apply_apply, smul_smul]
  rw [← Complex.coe_smul, smul_smul]

end ReciprocityTheory.ChartRestriction.DS.Mult1
