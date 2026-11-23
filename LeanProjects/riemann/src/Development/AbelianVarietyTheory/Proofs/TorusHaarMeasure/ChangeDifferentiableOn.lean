import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.WeightFunctionOnFrames
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.LUStatementPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.FundSetPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.OmFConnPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.OntoStatementPfC
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.OntoStatementPfD
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.InterpStatementPfH
import ReciprocityTheory.L2DbarEstimates.LeviForms.CovDet

namespace GlobalTheory.MeasInv

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates
  MeasureTheory Topology ReciprocityTheory.ChartRestriction.G.AR.Up.ExtFPf
open scoped ContDiff ENNReal Matrix

noncomputable section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} {X : Data E r}

theorem differentiable_cpt (x0 : Frame X.Ψ r) : Differentiable ℂ (cpt X x0) :=
  differentiable_pi.2 fun τ => differentiable_pi.2 fun a => differentiable_pi.2 fun b =>
    (IW.cpt_entry_cd X x0 τ a b).differentiable (by simp)

def overlap (x0 : Frame X.Ψ r) {x1 : Frame X.Ψ r} (D1 : LUData X x1) : Set (V (nd X)) :=
  {z | z ∈ OmF X x0 ∧ D1.Δ (cpt X x0 z) ≠ 0}

variable {x0 x1 : Frame X.Ψ r}

theorem isOpen_overlap (D1 : LUData X x1) : IsOpen (overlap x0 D1) :=
  (isOpen_cell D1).preimage (differentiable_cpt x0).continuous

theorem overlap_nonempty (h0 : IsOrth X x0) (D0 : LUData X x0) (D1 : LUData X x1) :
    ∃ z ∈ OmF X x0, D1.Δ (cpt X x0 z) ≠ 0 := by
  have hz0 := IW.zero_mem_OmF X x0 h0
  have hc : cpt X x0 0 ∈ cell D0 := ⟨hz0, (cpt_cell D0 hz0).1⟩
  obtain ⟨ε, hε, hB⟩ := Metric.isOpen_iff.1 (isOpen_cell D0) _ hc
  obtain ⟨y, hy, hy1⟩ := D1.dense _ hz0 ε hε
  obtain ⟨hyd, hy0⟩ := hB hy
  obtain ⟨hz, hb, he⟩ := D0.split y hyd hy0
  exact ⟨_, hz, cell_of_rmul D1 hz hb (he ▸ hy1)⟩

theorem overlap_ae_eq (h0 : IsOrth X x0) (D0 : LUData X x0) (D1 : LUData X x1) :
    overlap x0 D1 =ᵐ[volume] OmF X x0 := by
  have hnull := OntoD.null_zero (g := fun z => D1.Δ (cpt X x0 z)) (ExF.isOpen_OmF X x0)
    (OmFConnStatement_holds r X x0 h0)
    (D1.hΔ.comp (differentiable_cpt x0)).differentiableOn (overlap_nonempty h0 D0 D1)
  rw [ae_eq_set]
  refine ⟨?_, ?_⟩
  · rw [Set.diff_eq_empty.2 fun z hz => hz.1]
    exact measure_empty
  · refine measure_mono_null (fun z hz => ?_) hnull
    refine Set.mem_inter hz.1 ?_
    by_contra h
    exact hz.2 ⟨hz.1, h⟩

theorem lintegral_muF_overlap (h0 : IsOrth X x0) (D0 : LUData X x0) (D1 : LUData X x1)
    (g : V (nd X) → ℝ≥0∞) :
    ∫⁻ z, g z ∂muF X x0 = ∫⁻ z in overlap x0 D1, ENNReal.ofReal (densF X x0 z) * g z := by
  unfold muF
  rw [lintegral_withDensity_eq_lintegral_mul_non_measurable _
    (OntoC.measurable_densF X x0) (Filter.Eventually.of_forall fun _ => ENNReal.ofReal_lt_top),
    Measure.restrict_congr_set (overlap_ae_eq h0 D0 D1)]
  rfl

theorem change_mem (D0 : LUData X x0) (D1 : LUData X x1) {z : V (nd X)} (hz : z ∈ overlap x0 D1) :
    D1.zOf (cpt X x0 z) ∈ overlap x1 D0 ∧ D0.zOf (cpt X x1 (D1.zOf (cpt X x0 z))) = z := by
  obtain ⟨hw, hb, he⟩ := D1.split _ hz.1 hz.2
  obtain ⟨hΔ, hzz, -⟩ := cpt_cell D0 hz.1
  have h1 : D0.Δ (cpt X x1 (D1.zOf (cpt X x0 z))) ≠ 0 := cell_of_rmul D0 hw hb (he ▸ hΔ)
  refine ⟨⟨hw, h1⟩, ?_⟩
  rw [← (cell_rmul D0 hw h1 hb).2.1, ← he, hzz]

theorem change_image (D0 : LUData X x0) (D1 : LUData X x1) :
    (fun z => D1.zOf (cpt X x0 z)) '' overlap x0 D1 = overlap x1 D0 := by
  ext w
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact (change_mem D0 D1 hz).1
  · intro hw
    exact ⟨_, (change_mem D1 D0 hw).1, (change_mem D1 D0 hw).2⟩

theorem change_injOn (D0 : LUData X x0) (D1 : LUData X x1) :
    Set.InjOn (fun z => D1.zOf (cpt X x0 z)) (overlap x0 D1) := by
  intro z hz z' hz' h
  have h' : D1.zOf (cpt X x0 z) = D1.zOf (cpt X x0 z') := h
  rw [← (change_mem D0 D1 hz).2, h', (change_mem D0 D1 hz').2]

theorem change_differentiableOn (D1 : LUData X x1) :
    DifferentiableOn ℂ (fun z => D1.zOf (cpt X x0 z)) (overlap x0 D1) :=
  D1.hz.comp (differentiable_cpt x0).differentiableOn fun _ hz => hz

theorem densF_mul_nfac_sq (h0 : IsOrth X x0) {z : V (nd X)} (hz : z ∈ OmF X x0) :
    densF X x0 z * X.nfac (kapW X) (cpt X x0 z) ^ 2 = 1 := by
  have hN := FlowCoefficientBounds.nfac_pos X hz (kapW X)
  have hd := OntoB.densF_pos hz
  have h := IW.phla_kapW_cpt X x0 h0 hz
  unfold phla at h
  rw [← Real.exp_log hd, ← h, ← Real.exp_log (pow_pos hN 2), ← Real.exp_add, Real.log_pow]
  simp

theorem densF_change (hN : NfacRmulStatement (E := E)) (h0 : IsOrth X x0) (h1 : IsOrth X x1)
    {z w : V (nd X)} (hz : z ∈ OmF X x0) (hw : w ∈ OmF X x1) {b : Frame X.Ψ r} (hb : b ∈ Bor X.Ψ r)
    (he : cpt X x0 z = rmul (cpt X x1 w) b) :
    densF X x0 z = ‖bchar (kapW X) b‖ ^ 2 * densF X x1 w := by
  have e0 := densF_mul_nfac_sq h0 hz
  have e1 := densF_mul_nfac_sq h1 hw
  rw [he, hN r X (kapW X) _ hw b hb] at e0
  have hc : ‖bchar (kapW X) b‖ ≠ 0 := by
    intro h
    rw [h] at e0
    simp at e0
  calc densF X x0 z = densF X x0 z * (densF X x1 w * X.nfac (kapW X) (cpt X x1 w) ^ 2) := by
        rw [e1, mul_one]
    _ = ‖bchar (kapW X) b‖ ^ 2 * densF X x1 w *
        (densF X x0 z * (‖bchar (kapW X) b‖⁻¹ * X.nfac (kapW X) (cpt X x1 w)) ^ 2) := by
        field_simp
    _ = _ := by rw [e0, mul_one]

end

end GlobalTheory.MeasInv

namespace GlobalTheory

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates
  MeasureTheory Topology ReciprocityTheory.ChartRestriction.G.AR.Up.ExtFPf MeasInv
open scoped ContDiff ENNReal Matrix

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem measInv_of_jacobian (hK : KapGGStatement (E := E))
    (hN : NfacRmulStatement (E := E) ∧ NfacLactStatement (E := E) ∧ PnormInvStatement (E := E)) :
    MeasInvStatement (E := E) := by
  intro r X x0 x1 h0 h1 φ hφ hinv
  obtain ⟨D0⟩ := luData_of lu_holds X x0 h0
  obtain ⟨D1⟩ := luData_of lu_holds X x1 h1
  have hmeas : Measurable fun w => ENNReal.ofReal (densF X x1 w) * φ (cpt X x1 w) :=
    (OntoC.measurable_densF X x1).mul (hφ.comp (differentiable_cpt x1).continuous.measurable)
  rw [lintegral_muF_overlap h0 D0 D1, lintegral_muF_overlap h1 D1 D0, ← change_image D0 D1,
    I.cov (nd X) _ _ _ (isOpen_overlap D1) (change_differentiableOn D1) (change_injOn D0 D1) hmeas]
  have hdet := hK r X x0 x1 1 _ _ (fun z => D1.bOf (cpt X x0 z)) (isOpen_overlap D1)
    (change_differentiableOn D1) fun z hz => by
      obtain ⟨-, hb, he⟩ := D1.split _ hz.1 hz.2
      exact ⟨hz.1, hb, by rw [FundSetPf.lact_one]; exact he⟩
  refine setLIntegral_congr_fun (isOpen_overlap D1).measurableSet fun z hz => ?_
  obtain ⟨hw, hb, he⟩ := D1.split _ hz.1 hz.2
  have hd : LinearMap.det (fderiv ℂ (fun z => D1.zOf (cpt X x0 z)) z : V (nd X) →ₗ[ℂ] V (nd X)) =
      bchar (kapW X) (D1.bOf (cpt X x0 z)) := hdet z hz
  have hφe : φ (cpt X x0 z) = φ (cpt X x1 (D1.zOf (cpt X x0 z))) := by
    rw [← hinv _ hw _ hb, ← he]
  beta_reduce
  rw [hd, densF_change hN.1 h0 h1 hz.1 hw hb he, ENNReal.ofReal_mul (by positivity), hφe, mul_assoc]

end GlobalTheory
