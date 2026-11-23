import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.KaUnfoldPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.MeasInvStatementPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.FundSetMeasStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.DivStartPf

namespace ReciprocityTheory.ChartRestriction.G.AR.Up.FSM

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ENNReal

noncomputable section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

private theorem rmul_rmul' {Ψ : Finset (E →+* ℂ)} (x a b : Frame Ψ r) :
    rmul (rmul x a) b = rmul x (rmul a b) := by
  funext τ
  exact Matrix.mul_assoc (mat x τ) (mat a τ) (mat b τ)

private theorem rmul_mem_bor_upper_bounds {Ψ : Finset (E →+* ℂ)} {a b : Frame Ψ r} (ha : a ∈ Bor Ψ r)
    (hb : b ∈ Bor Ψ r) : rmul a b ∈ Bor Ψ r := by
  simp only [Bor, Set.mem_setOf_eq] at ha hb ⊢
  intro τ
  obtain ⟨ha1, ha2⟩ := ha τ
  obtain ⟨hb1, hb2⟩ := hb τ
  have hA : Matrix.BlockTriangular (mat a τ) id := by
    intro i j h
    exact ha2 i j h
  have hB : Matrix.BlockTriangular (mat b τ) id := by
    intro i j h
    exact hb2 i j h
  refine ⟨?_, fun i j h => hA.mul hB h⟩
  show (mat a τ * mat b τ).det ≠ 0
  rw [Matrix.det_mul]
  exact mul_ne_zero ha1 hb1

private theorem mem_bor_of_mat_eq_inv {Ψ : Finset (E →+* ℂ)} {b c : Frame Ψ r} (hb : b ∈ Bor Ψ r)
    (hc : ∀ τ, mat c τ = (mat b τ)⁻¹) : c ∈ Bor Ψ r := by
  simp only [Bor, Set.mem_setOf_eq] at hb ⊢
  intro τ
  obtain ⟨hb1, hb2⟩ := hb τ
  have hB : Matrix.BlockTriangular (mat b τ) id := by
    intro i j h
    exact hb2 i j h
  haveI : Invertible (mat b τ) := Matrix.invertibleOfIsUnitDet _ (isUnit_iff_ne_zero.mpr hb1)
  have hI : Matrix.BlockTriangular (mat b τ)⁻¹ id := Matrix.blockTriangular_inv_of_blockTriangular hB
  refine ⟨?_, fun i j h => ?_⟩
  · rw [hc τ]
    exact (Matrix.isUnit_nonsing_inv_det _ (isUnit_iff_ne_zero.mpr hb1)).ne_zero
  · have h2 := hI h
    rw [← hc τ] at h2
    exact h2

private theorem rmul_rmul_of_mat_eq_inv {Ψ : Finset (E →+* ℂ)} (x : Frame Ψ r) {b c : Frame Ψ r} (hb : b ∈ Bor Ψ r)
    (hc : ∀ τ, mat c τ = (mat b τ)⁻¹) : rmul (rmul x b) c = x := by
  simp only [Bor, Set.mem_setOf_eq] at hb
  funext τ
  have h := isUnit_iff_ne_zero.mpr (hb τ).1
  show mat x τ * mat b τ * mat c τ = x τ
  rw [hc τ, Matrix.mul_nonsing_inv_cancel_right _ _ h]
  rfl

private theorem lact_rmul_upper_bounds {Ψ : Finset (E →+* ℂ)} (γ : GL (Fin r) E) (x b : Frame Ψ r) :
    lact γ (rmul x b) = rmul (lact γ x) b := by
  funext τ
  exact (Matrix.mul_assoc ((γ : Matrix (Fin r) (Fin r) E).map τ.1) (mat x τ) (mat b τ)).symm

private theorem lact_lact' {Ψ : Finset (E →+* ℂ)} (γ δ : GL (Fin r) E) (x : Frame Ψ r) :
    lact γ (lact δ x) = lact (γ * δ) x := by
  funext τ
  show (γ : Matrix (Fin r) (Fin r) E).map τ.1 * ((δ : Matrix (Fin r) (Fin r) E).map τ.1 * mat x τ) =
    ((γ * δ : GL (Fin r) E) : Matrix (Fin r) (Fin r) E).map τ.1 * mat x τ
  rw [Units.val_mul, Matrix.map_mul, Matrix.mul_assoc]

private theorem lact_inv_lact_upper_bounds {Ψ : Finset (E →+* ℂ)} (γ : GL (Fin r) E) (x : Frame Ψ r) :
    lact γ⁻¹ (lact γ x) = x := by
  rw [lact_lact', inv_mul_cancel]
  funext τ
  show ((1 : GL (Fin r) E) : Matrix (Fin r) (Fin r) E).map τ.1 * mat x τ = x τ
  rw [Units.val_one, Matrix.map_one _ (map_zero τ.1) (map_one τ.1), Matrix.one_mul]
  try rfl

theorem atMostOnce (X : Data E r) {x0 : Frame X.Ψ r} (ho : IsOrth X x0) {FF : Set (V (nd X))}
    (hFF : IsFundSet X x0 FF) (y : Frame X.Ψ r) :
    ∑' γ : X.Γ, (KU.Sset X x0 FF).indicator (1 : Frame X.Ψ r → ℝ≥0∞) (lact γ.1 y) ≤ 1 := by
  unfold IsFundSet at hFF
  obtain ⟨_, hFO, hFinj, _⟩ := hFF
  have hS : ∀ w, w ∈ KU.Sset X x0 FF → ∃ z ∈ FF, ∃ b ∈ Bor X.Ψ r, w = rmul (cpt X x0 z) b := by
    intro w hw
    simp only [KU.Sset] at hw
    obtain ⟨⟨z, b⟩, ⟨hz, hb⟩, he⟩ := hw
    exact ⟨z, hz, b, hb, he.symm⟩
  have huniq : ∀ γ γ0 : X.Γ, lact γ.1 y ∈ KU.Sset X x0 FF → lact γ0.1 y ∈ KU.Sset X x0 FF →
      γ = γ0 := by
    intro γ γ0 h1 h2
    obtain ⟨z, hz, b, hb, hzb⟩ := hS _ h1
    obtain ⟨z0, hz0, b0, hb0, hzb0⟩ := hS _ h2
    have hg : γ.1 * γ0.1⁻¹ ∈ X.Γ := X.Γ.mul_mem γ.2 (X.Γ.inv_mem γ0.2)
    have hy : y = lact γ0.1⁻¹ (rmul (cpt X x0 z0) b0) := by
      rw [← hzb0, lact_inv_lact_upper_bounds]
    have hst : rmul (lact (γ.1 * γ0.1⁻¹) (cpt X x0 z0)) b0 = rmul (cpt X x0 z) b := by
      rw [← lact_rmul_upper_bounds, ← lact_lact', ← hy, hzb]
    obtain ⟨bi, hbi⟩ : ∃ c : Frame X.Ψ r, ∀ τ, mat c τ = (mat b τ)⁻¹ :=
      ⟨(fun τ => ((mat b τ)⁻¹ : Matrix (Fin r) (Fin r) ℂ)), fun τ => rfl⟩
    obtain ⟨bi0, hbi0⟩ : ∃ c : Frame X.Ψ r, ∀ τ, mat c τ = (mat b0 τ)⁻¹ :=
      ⟨(fun τ => ((mat b0 τ)⁻¹ : Matrix (Fin r) (Fin r) ℂ)), fun τ => rfl⟩
    have hw : cpt X x0 z = lact (γ.1 * γ0.1⁻¹) (rmul (cpt X x0 z0) (rmul b0 bi)) := by
      rw [lact_rmul_upper_bounds, ← rmul_rmul', hst, rmul_rmul_of_mat_eq_inv _ hb hbi]
    have hzz : z0 = z := hFinj z0 hz0 z hz _ hg _ (rmul_mem_bor_upper_bounds hb0 (mem_bor_of_mat_eq_inv hb hbi)) hw
    subst hzz
    have hw0 : cpt X x0 z0 ∈ X.dom := hFO hz0
    have hfix : lact (γ.1 * γ0.1⁻¹) (cpt X x0 z0) = rmul (cpt X x0 z0) (rmul b bi0) := by
      rw [← rmul_rmul', ← hst, rmul_rmul_of_mat_eq_inv _ hb0 hbi0]
    have hg1 : γ.1 * γ0.1⁻¹ = 1 := X.Γ_free _ hg _ hw0 _ (rmul_mem_bor_upper_bounds hb (mem_bor_of_mat_eq_inv hb0 hbi0)) hfix
    exact Subtype.ext (mul_inv_eq_one.mp hg1)
  by_cases hex : ∃ γ0 : X.Γ, lact γ0.1 y ∈ KU.Sset X x0 FF
  · obtain ⟨γ0, hγ0⟩ := hex
    rw [tsum_eq_single γ0]
    · rw [Set.indicator_of_mem hγ0]
      simp
    · intro γ hne
      exact Set.indicator_apply_eq_zero.mpr fun hm => absurd (huniq γ γ0 hm hγ0) hne
  · push_neg at hex
    have h0 : ∀ γ : X.Γ, (KU.Sset X x0 FF).indicator (1 : Frame X.Ψ r → ℝ≥0∞) (lact γ.1 y) = 0 :=
      fun γ => Set.indicator_apply_eq_zero.mpr fun hm => absurd hm (hex γ)
    rw [tsum_congr h0, tsum_zero]
    exact zero_le_one

end

theorem fundSetMeasStatement_of_isCMField {E : Type} [Field E] [NumberField E] [IsCMField E] :
    FundSetMeasStatement (E := E) := by
  intro r X x0 FF ho hFF ⟨x1, ho1, CechHodgeFiltration, hFF1, hfin⟩
  classical
  have := KU.countable_Γ X
  have hM := measInv_holds (E := E)
  have hS : MeasurableSet (KU.Sset X x0 FF) := KU.meas_S X ho hFF.1
  have hS1 : MeasurableSet (KU.Sset X x1 CechHodgeFiltration) := KU.meas_S X ho1 hFF1.1
  have hcpt0 := (KU.cont_cpt X x0).measurable
  have hcpt1 := (KU.cont_cpt X x1).measurable

  set Bad : Set (Frame X.Ψ r) := ⋂ γ : X.Γ, (lact γ.1⁻¹ ⁻¹' KU.Sset X x1 CechHodgeFiltration)ᶜ with hBaddef
  have hBad : MeasurableSet Bad :=
    MeasurableSet.iInter fun γ => ((KU.cont_lact X γ.1⁻¹).measurable hS1).compl
  have hBadB : ∀ x ∈ X.dom, ∀ b ∈ Bor X.Ψ r,
      Bad.indicator (1 : Frame X.Ψ r → ℝ≥0∞) (rmul x b) = Bad.indicator 1 x := by
    intro x _ b hb
    have e : rmul x b ∈ Bad ↔ x ∈ Bad := by
      simp only [hBaddef, Set.mem_iInter, Set.mem_compl_iff, Set.mem_preimage, KU.lact_rmul',
        KU.rmul_mem_S X hb]
    by_cases h : x ∈ Bad
    · rw [Set.indicator_of_mem h, Set.indicator_of_mem (e.mpr h)]; rfl
    · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem (fun h' => h (e.mp h'))]
  have h1 : ∫⁻ z, Bad.indicator 1 (cpt X x1 z) ∂muF X x1 = 0 := by
    have hm : Measurable fun z => Bad.indicator (1 : Frame X.Ψ r → ℝ≥0∞) (cpt X x1 z) :=
      (measurable_one.indicator hBad).comp hcpt1
    rw [lintegral_eq_zero_iff hm]
    filter_upwards [KU.cover X hFF1] with z ⟨γ, hγ, hSz⟩
    have : cpt X x1 z ∉ Bad := fun h => (Set.mem_iInter.mp h ⟨γ, hγ⟩) hSz
    simp [Set.indicator_of_notMem this]
  have h0 : ∫⁻ z, Bad.indicator 1 (cpt X x0 z) ∂muF X x0 = 0 := by
    rw [hM r X x0 x1 ho ho1 _ (measurable_one.indicator hBad) hBadB]; exact h1
  have hcov : ∀ᵐ z ∂muF X x0, cpt X x0 z ∉ Bad := by
    have hm : Measurable fun z => Bad.indicator (1 : Frame X.Ψ r → ℝ≥0∞) (cpt X x0 z) :=
      (measurable_one.indicator hBad).comp hcpt0
    have := (lintegral_eq_zero_iff hm).mp h0
    filter_upwards [this] with z hz hb
    simp [Set.indicator_of_mem hb] at hz

  let H : X.Γ → Frame X.Ψ r → ℝ≥0∞ := fun γ y =>
    (KU.Sset X x0 FF).indicator 1 y * (lact γ.1⁻¹ ⁻¹' KU.Sset X x1 CechHodgeFiltration).indicator 1 y
  have hHm : ∀ γ, Measurable (H γ) := fun γ =>
    (measurable_one.indicator hS).mul (measurable_one.indicator ((KU.cont_lact X γ.1⁻¹).measurable hS1))
  have hHB : ∀ γ, ∀ x ∈ X.dom, ∀ b ∈ Bor X.Ψ r, H γ (rmul x b) = H γ x := by
    intro γ x _ b hb
    have e1 : rmul x b ∈ KU.Sset X x0 FF ↔ x ∈ KU.Sset X x0 FF := KU.rmul_mem_S X hb
    have e2 : rmul x b ∈ lact γ.1⁻¹ ⁻¹' KU.Sset X x1 CechHodgeFiltration ↔ x ∈ lact γ.1⁻¹ ⁻¹' KU.Sset X x1 CechHodgeFiltration := by
      simp only [Set.mem_preimage, KU.lact_rmul', KU.rmul_mem_S X hb]
    simp only [H, Set.indicator_apply, e1, e2, Pi.one_apply]
  have step1 : muF X x0 FF = ∫⁻ z, (KU.Sset X x0 FF).indicator 1 (cpt X x0 z) ∂muF X x0 := by
    rw [← lintegral_indicator_one hFF.1]
    refine lintegral_congr fun z => ?_
    by_cases hz : z ∈ FF
    · rw [Set.indicator_of_mem hz, Set.indicator_of_mem ((KU.cpt_mem_S X ho z).mpr hz)]; rfl
    · rw [Set.indicator_of_notMem hz, Set.indicator_of_notMem (fun h => hz ((KU.cpt_mem_S X ho z).mp h))]
  have step2 : ∫⁻ z, (KU.Sset X x0 FF).indicator 1 (cpt X x0 z) ∂muF X x0 ≤
      ∫⁻ z, ∑' γ : X.Γ, H γ (cpt X x0 z) ∂muF X x0 := by
    refine lintegral_mono_ae (hcov.mono fun z hz => ?_)
    by_cases hS0 : cpt X x0 z ∈ KU.Sset X x0 FF
    · have : ∃ γ : X.Γ, cpt X x0 z ∈ lact γ.1⁻¹ ⁻¹' KU.Sset X x1 CechHodgeFiltration := by
        by_contra hn
        push_neg at hn
        exact hz (Set.mem_iInter.mpr fun γ => hn γ)
      obtain ⟨γ, hγ⟩ := this
      refine le_trans (le_of_eq ?_) (ENNReal.le_tsum γ)
      simp only [H, Set.indicator_of_mem hS0, Set.indicator_of_mem hγ, Pi.one_apply, mul_one]
    · rw [Set.indicator_of_notMem hS0]; exact bot_le
  have step3 : ∫⁻ z, ∑' γ : X.Γ, H γ (cpt X x0 z) ∂muF X x0 = ∑' γ : X.Γ, ∫⁻ z, H γ (cpt X x0 z) ∂muF X x0 :=
    lintegral_tsum fun γ => ((hHm γ).comp hcpt0).aemeasurable
  have hae1 : ∀ᵐ z ∂muF X x1, z ∈ OmF X x1 := ExtFPf.ae_OmF (X := X) (x0 := x1)
  have step4 : ∀ γ : X.Γ, ∫⁻ z, H γ (cpt X x0 z) ∂muF X x0 =
      ∫⁻ z, CechHodgeFiltration.indicator (fun z => (KU.Sset X x0 FF).indicator (1 : Frame X.Ψ r → ℝ≥0∞)
        (lact γ.1 (cpt X x1 z))) z ∂muF X x1 := by
    intro γ
    rw [hM r X x0 (lact γ.1 x1) ho (KU.isOrth_lact X γ.2 ho1) (H γ) (hHm γ) (hHB γ), KU.muF_lact X γ.2]
    refine lintegral_congr fun z => ?_
    rw [KU.cpt_lact]
    simp only [H]
    have e : lact γ.1 (cpt X x1 z) ∈ lact γ.1⁻¹ ⁻¹' KU.Sset X x1 CechHodgeFiltration ↔ z ∈ CechHodgeFiltration := by
      rw [Set.mem_preimage, KU.lact_lact, inv_mul_cancel, KU.lact_one, KU.cpt_mem_S X ho1]
    by_cases hz : z ∈ CechHodgeFiltration
    · rw [Set.indicator_of_mem (e.mpr hz), Set.indicator_of_mem hz, Pi.one_apply, mul_one]
    · rw [Set.indicator_of_notMem (fun h => hz (e.mp h)), Set.indicator_of_notMem hz, mul_zero]
  have hI : ∀ γ : X.Γ, Measurable fun z => CechHodgeFiltration.indicator (fun z => (KU.Sset X x0 FF).indicator
      (1 : Frame X.Ψ r → ℝ≥0∞) (lact γ.1 (cpt X x1 z))) z := fun γ =>
    ((measurable_one.indicator hS).comp ((KU.cont_lact X γ.1).comp (KU.cont_cpt X x1)).measurable).indicator hFF1.1
  have step5 : ∑' γ : X.Γ, ∫⁻ z, CechHodgeFiltration.indicator (fun z => (KU.Sset X x0 FF).indicator (1 : Frame X.Ψ r → ℝ≥0∞)
      (lact γ.1 (cpt X x1 z))) z ∂muF X x1 ≤ muF X x1 CechHodgeFiltration := by
    rw [← lintegral_tsum fun γ => (hI γ).aemeasurable, ← lintegral_indicator_one hFF1.1]
    refine lintegral_mono fun z => ?_
    by_cases hz : z ∈ CechHodgeFiltration
    · simp only [Set.indicator_of_mem hz, Pi.one_apply]
      exact FSM.atMostOnce X ho hFF _
    · simp [Set.indicator_of_notMem hz]
  calc muF X x0 FF = _ := step1
    _ ≤ _ := step2
    _ = _ := step3
    _ = _ := tsum_congr step4
    _ ≤ muF X x1 CechHodgeFiltration := step5
    _ < ⊤ := hfin

end ReciprocityTheory.ChartRestriction.G.AR.Up.FSM

namespace ReciprocityTheory.ChartRestriction.G.AR.Up

open NumberField

theorem FundSetMeasStatement_holds {E : Type} [Field E] [NumberField E] [IsCMField E] :
    FundSetMeasStatement (E := E) := FSM.fundSetMeasStatement_of_isCMField

theorem DivStartStatement_holds {E : Type} [Field E] [NumberField E] [IsCMField E] :
    DivStartStatement (E := E) := DivSt.divStart_of FundSetMeasStatement_holds

end ReciprocityTheory.ChartRestriction.G.AR.Up
