import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.ExtFStatementPfB
import ReciprocityTheory.L2DbarEstimates.NormFibrations.MvBlowup

namespace ReciprocityTheory.ChartRestriction.G.AR.Up.ExtFPf

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.L2DbarEstimates MeasureTheory Topology Metric
open scoped ENNReal Matrix

noncomputable section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} {X : Data E r}

def chartE (X : Data E r) : Frame X.Ψ r ≃L[ℂ] V (Module.finrank ℂ (Frame X.Ψ r)) :=
  ContinuousLinearEquiv.ofFinrankEq (finrank_euclideanSpace_fin).symm

theorem haar_frame (X : Data E r) : (volume : Measure (Frame X.Ψ r)).IsAddHaarMeasure := by
  haveI h0 : (volume : Measure ℂ).IsAddHaarMeasure := inferInstance
  haveI h0' : SigmaFinite (volume : Measure ℂ) := inferInstance
  haveI h1 : (volume : Measure (Fin r → ℂ)).IsAddHaarMeasure := by
    rw [volume_pi]; exact Measure.pi.isAddHaarMeasure _
  haveI h2 : (volume : Measure (Fin r → Fin r → ℂ)).IsAddHaarMeasure := by
    rw [volume_pi]; exact Measure.pi.isAddHaarMeasure _
  rw [volume_pi]; exact Measure.pi.isAddHaarMeasure _

theorem vol_eq (X : Data E r) :
    ∃ c : ℝ≥0∞, c < ⊤ ∧ (volume : Measure (V (Module.finrank ℂ (Frame X.Ψ r)))) =
      c • Measure.map (chartE X).toHomeomorph.toMeasurableEquiv volume := by
  haveI := haar_frame X
  haveI : (Measure.map (chartE X) (volume : Measure (Frame X.Ψ r))).IsAddHaarMeasure :=
    (chartE X).isAddHaarMeasure_map volume
  have h := Measure.isAddLeftInvariant_eq_smul (volume : Measure (V (Module.finrank ℂ (Frame X.Ψ r))))
    (Measure.map (chartE X) (volume : Measure (Frame X.Ψ r)))
  refine ⟨(volume : Measure (V (Module.finrank ℂ (Frame X.Ψ r)))).addHaarScalarFactor
    (Measure.map (chartE X) volume), ENNReal.coe_lt_top, ?_⟩
  calc (volume : Measure (V (Module.finrank ℂ (Frame X.Ψ r)))) = _ := h
    _ = _ := by rw [ENNReal.smul_def]; rfl

theorem lint_transfer (X : Data E r) (S : Set (V (Module.finrank ℂ (Frame X.Ψ r))))
    (g : V (Module.finrank ℂ (Frame X.Ψ r)) → ℝ≥0∞) :
    ∃ c : ℝ≥0∞, c < ⊤ ∧ ∫⁻ y in S, g y = c * ∫⁻ x in (chartE X) ⁻¹' S, g (chartE X x) := by
  obtain ⟨c, hc, hv⟩ := vol_eq X
  refine ⟨c, hc, ?_⟩
  rw [hv, Measure.restrict_smul, lintegral_smul_measure, MeasurableEquiv.restrict_map, lintegral_map_equiv]
  rfl

variable {x0 : Frame X.Ψ r} (D : LUData X x0) (la : Wt X.Ψ r) (F : V (nd X) → ℂ)

theorem local_ext (hM : FrameMeasStatement (E := E)) (hx0 : IsOrth X x0)
    (hF : DifferentiableOn ℂ F (OmF X x0))
    (hL2 : ∀ C : Set (Frame X.Ψ r), IsCompact C → C ⊆ X.dom →
      ∫⁻ z in sat X x0 C, ENNReal.ofReal (‖F z‖ ^ 2 * Real.exp (-phla X la (cpt X x0 z))) ∂muF X x0 < ⊤)
    {x : Frame X.Ψ r} (hx : x ∈ X.dom) :
    ∃ ρ > 0, (∀ y, chartE X y ∈ closedBall (chartE X x) ρ → y ∈ X.dom) ∧
      ∃ U : V (Module.finrank ℂ (Frame X.Ψ r)) → ℂ, DifferentiableOn ℂ U (ball (chartE X x) ρ) ∧
        ∀ y, chartE X y ∈ ball (chartE X x) ρ → D.Δ y ≠ 0 → U (chartE X y) = P0 D la F y := by
  have hO : IsOpen ((chartE X).symm ⁻¹' X.dom) :=
    (FourierCoefficientDomain.isOpen_dom X).preimage (chartE X).symm.continuous
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hO (chartE X x) (by simpa using hx)
  have hsub : ∀ y, chartE X y ∈ closedBall (chartE X x) (ε / 2) → y ∈ X.dom := fun y hy => by
    have := hball (closedBall_subset_ball (by linarith) hy)
    simpa using this
  refine ⟨ε / 2, by positivity, hsub, ?_⟩
  have hC : IsCompact ((chartE X) ⁻¹' closedBall (chartE X x) (ε / 2)) :=
    (chartE X).toHomeomorph.isCompact_preimage.mpr (isCompact_closedBall _ _)
  have hCd : (chartE X) ⁻¹' closedBall (chartE X x) (ε / 2) ⊆ X.dom := fun y hy => hsub y hy
  have hint := poincareLift_locally_squareIntegrable D la F hM hx0 hF hL2 hC hCd
  obtain ⟨c, hc, htr⟩ := lint_transfer X (closedBall (chartE X x) (ε / 2))
    (fun w => ENNReal.ofReal (‖P0 D la F ((chartE X).symm w)‖ ^ 2))
  have hfin : ∫⁻ w in ball (chartE X x) (ε / 2) \ {w | D.Δ ((chartE X).symm w) = 0},
      ENNReal.ofReal (‖P0 D la F ((chartE X).symm w)‖ ^ 2) < ⊤ := by
    refine lt_of_le_of_lt (lintegral_mono_set (Set.sdiff_subset.trans ball_subset_closedBall)) ?_
    rw [htr]
    simp only [ContinuousLinearEquiv.symm_apply_apply]
    exact ENNReal.mul_lt_top hc hint
  have hΔd : DifferentiableOn ℂ (fun w => D.Δ ((chartE X).symm w)) (ball (chartE X x) (ε / 2)) :=
    (D.hΔ.comp (chartE X).symm.differentiable).differentiableOn
  have hud : DifferentiableOn ℂ (fun w => P0 D la F ((chartE X).symm w))
      (ball (chartE X x) (ε / 2) \ {w | D.Δ ((chartE X).symm w) = 0}) := by
    refine (poincareLift_differentiableOn D la F hF).comp (chartE X).symm.differentiable.differentiableOn fun w hw => ?_
    refine ⟨hsub _ ?_, hw.2⟩
    simpa using ball_subset_closedBall hw.1
  obtain ⟨U, hU, hUe⟩ := ReciprocityTheory.L2DbarEstimates.ext _ (chartE X x) (ε / 2) _ _ hΔd hud hfin
  refine ⟨U, hU, fun y hy hΔ => ?_⟩
  have := hUe ⟨hy, by simpa using hΔ⟩
  simpa using this

theorem dense_cell {x : Frame X.Ψ r} (hx : x ∈ X.dom) : x ∈ closure (cell D) := by
  have hmat : ∀ τ : X.Ψ, Continuous fun x : Frame X.Ψ r => mat x τ := fun τ =>
    continuous_pi fun i => continuous_pi fun j =>
      (continuous_apply j).comp ((continuous_apply i).comp (continuous_apply τ))
  have hgram : ∀ τ : X.Ψ, Continuous fun x : Frame X.Ψ r => gram τ.1 X.Gm (mat x τ) := by
    intro τ
    refine continuous_pi fun a => continuous_pi fun b => ?_
    simp only [gram, Matrix.of_apply, hermC, col, mat, starRingEnd_apply]
    fun_prop
  have hopen : IsOpen X.dom := by
    have e : X.dom = ⋂ τ : X.Ψ, ({x | (mat x τ).det ≠ 0} ∩
        ⋂ i : Fin (r + 1), {x | 0 < psgn X.p0 i * (dmin X.Gm x τ i).re}) := by
      ext x; simp [Data.dom, GG]
    rw [e]
    refine isOpen_iInter_of_finite fun τ => IsOpen.inter ?_ (isOpen_iInter_of_finite fun i => ?_)
    · exact isOpen_ne_fun (hmat τ).matrix_det continuous_const
    · refine isOpen_lt continuous_const (continuous_const.mul (Complex.continuous_re.comp ?_))
      exact ((hgram τ).matrix_submatrix _ _).matrix_det
  rw [Metric.mem_closure_iff]
  intro ε hε
  obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.1 hopen x hx
  obtain ⟨y, hy, hΔ⟩ := D.dense x hx (min ε δ) (lt_min hε hδ)
  refine ⟨y, (show y ∈ X.dom ∧ D.Δ y ≠ 0 from ⟨hball (Metric.ball_subset_ball (min_le_right _ _) hy), hΔ⟩), ?_⟩
  rw [dist_comm]
  exact lt_of_lt_of_le (Metric.mem_ball.1 hy) (min_le_left _ _)

theorem rmul_cont (b : Frame X.Ψ r) : Continuous fun x : Frame X.Ψ r => rmul x b := by
  refine continuous_pi fun τ => continuous_pi fun i => continuous_pi fun j => ?_
  simp only [rmul, mat, Matrix.mul_apply, Matrix.of_apply]
  fun_prop

end

end ReciprocityTheory.ChartRestriction.G.AR.Up.ExtFPf

namespace ReciprocityTheory.ChartRestriction.G.AR.Up

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.L2DbarEstimates MeasureTheory Topology Metric
  ReciprocityTheory.ChartRestriction.G.AR.Up.ExtFPf
open scoped ENNReal Matrix

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem extF_of (hLU : LUStatement (E := E)) (hM : FrameMeasStatement (E := E)) :
    ExtFStatement (E := E) := by
  intro r X x0 hx0 la F hF hL2
  obtain ⟨D⟩ := luData_of hLU X x0 hx0
  have hloc := fun (x : Frame X.Ψ r) (hx : x ∈ X.dom) => local_ext D la F hM hx0 hF hL2 hx
  choose ρ hρ hsub U hU hUeq using hloc
  classical

  have hagree : ∀ x (hx : x ∈ X.dom) y (hy : y ∈ X.dom) w, w ∈ ball (chartE X x) (ρ x hx) →
      w ∈ ball (chartE X y) (ρ y hy) → U x hx w = U y hy w := by
    intro x hx y hy w hwx hwy
    set T := ball (chartE X x) (ρ x hx) ∩ ball (chartE X y) (ρ y hy) with hT
    set s := T ∩ {w | D.Δ ((chartE X).symm w) ≠ 0} with hs
    have hTo : IsOpen T := isOpen_ball.inter isOpen_ball
    have heq : Set.EqOn (U x hx) (U y hy) s := by
      intro w' hw'
      have h1 := hUeq x hx ((chartE X).symm w') (by simpa using hw'.1.1) hw'.2
      have h2 := hUeq y hy ((chartE X).symm w') (by simpa using hw'.1.2) hw'.2
      simp only [ContinuousLinearEquiv.apply_symm_apply] at h1 h2
      rw [h1, h2]
    have hcl : T ⊆ closure s := by
      intro w' hw'
      rw [Metric.mem_closure_iff]
      intro δ hδ
      obtain ⟨δ0, hδ0, hb0⟩ := Metric.isOpen_iff.mp hTo w' hw'
      have hz : (chartE X).symm w' ∈ X.dom :=
        hsub x hx _ (by simpa using ball_subset_closedBall hw'.1)
      set κ := ‖((chartE X) : Frame X.Ψ r →L[ℂ] V (Module.finrank ℂ (Frame X.Ψ r)))‖ + 1 with hκ
      have hκ0 : 0 < κ := by positivity
      obtain ⟨y', hy', hΔ'⟩ := D.dense _ hz (min δ δ0 / κ) (by positivity)
      have hd : dist w' (chartE X y') < min δ δ0 := by
        have h1 : dist w' (chartE X y') = ‖(chartE X) ((chartE X).symm w' - y')‖ := by
          rw [map_sub, ContinuousLinearEquiv.apply_symm_apply, dist_eq_norm]
        rw [h1]
        calc ‖(chartE X) ((chartE X).symm w' - y')‖
            ≤ ‖((chartE X) : Frame X.Ψ r →L[ℂ] V (Module.finrank ℂ (Frame X.Ψ r)))‖ *
                ‖(chartE X).symm w' - y'‖ :=
              ((chartE X) : Frame X.Ψ r →L[ℂ] V (Module.finrank ℂ (Frame X.Ψ r))).le_opNorm _
          _ ≤ ‖((chartE X) : Frame X.Ψ r →L[ℂ] V (Module.finrank ℂ (Frame X.Ψ r)))‖ *
                (min δ δ0 / κ) := by
              gcongr
              rw [← dist_eq_norm, dist_comm]
              exact (mem_ball.mp hy').le
          _ < κ * (min δ δ0 / κ) := by
              gcongr
              rw [hκ]; linarith
          _ = min δ δ0 := by field_simp
      refine ⟨chartE X y', ⟨hb0 (mem_ball.mpr (by rw [dist_comm]; exact lt_of_lt_of_le hd (min_le_right _ _))),
        by simpa using hΔ'⟩, lt_of_lt_of_le hd (min_le_left _ _)⟩
    have := Set.EqOn.of_subset_closure heq ((hU x hx).continuousOn.mono Set.inter_subset_left)
      ((hU y hy).continuousOn.mono Set.inter_subset_right) Set.inter_subset_left hcl
    exact this ⟨hwx, hwy⟩
  set P : Frame X.Ψ r → ℂ := fun x => if hx : x ∈ X.dom then U x hx (chartE X x) else 0 with hP

  have hPcell : ∀ y ∈ cell D, P y = P0 D la F y := by
    intro y hy
    rw [hP]
    simp only [dif_pos hy.1]
    exact hUeq y hy.1 y (mem_ball_self (hρ y hy.1)) hy.2

  have hPd : DifferentiableOn ℂ P X.dom := by
    intro x hx
    have hev : P =ᶠ[𝓝 x] (fun y => U x hx (chartE X y)) := by
      have hO : (chartE X) ⁻¹' ball (chartE X x) (ρ x hx) ∈ 𝓝 x :=
        (isOpen_ball.preimage (chartE X).continuous).mem_nhds (mem_ball_self (hρ x hx))
      filter_upwards [hO] with y hy
      have hyd : y ∈ X.dom := hsub x hx y (ball_subset_closedBall hy)
      rw [hP]
      simp only [dif_pos hyd]
      exact (hagree x hx y hyd (chartE X y) hy (mem_ball_self (hρ y hyd))).symm
    have hd : DifferentiableAt ℂ (fun y => U x hx (chartE X y)) x :=
      ((hU x hx).differentiableAt (isOpen_ball.mem_nhds (mem_ball_self (hρ x hx)))).comp x
        (chartE X).differentiableAt
    exact (hd.congr_of_eventuallyEq hev).differentiableWithinAt
  refine ⟨P, ⟨hPd, fun x hx b hb => ?_⟩, fun z hz => ?_⟩
  · have heq : Set.EqOn (fun x => P (rmul x b)) (fun x => bchar la b * P x) (cell D) := by
      intro y hy
      obtain ⟨h1, -, -⟩ := cell_rmul D hy.1 hy.2 hb
      have hyb : rmul y b ∈ cell D := ⟨OrthogonalFrameDomain.rmul_mem_dom X hy.1 hb, h1⟩
      simp only
      rw [hPcell _ hyb, hPcell _ hy, poincareLift_borel_equivariant D la F hy.1 hb]
    have hc1 : ContinuousOn (fun x => P (rmul x b)) X.dom :=
      hPd.continuousOn.comp (rmul_cont b).continuousOn fun y hy => OrthogonalFrameDomain.rmul_mem_dom X hy hb
    have hc2 : ContinuousOn (fun x => bchar la b * P x) X.dom := continuousOn_const.mul hPd.continuousOn
    exact Set.EqOn.of_subset_closure heq hc1 hc2 (fun y hy => hy.1) (fun y hy => dense_cell D hy) hx
  · obtain ⟨h1, -, -⟩ := cpt_cell D hz
    rw [hPcell _ ⟨hz, h1⟩, poincareLift_on_chart D la F hz]

end ReciprocityTheory.ChartRestriction.G.AR.Up
