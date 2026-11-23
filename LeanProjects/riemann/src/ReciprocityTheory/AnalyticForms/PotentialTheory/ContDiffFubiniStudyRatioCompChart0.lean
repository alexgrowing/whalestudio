import ReciprocityTheory.AnalyticForms.PotentialTheory.ContDiffOnFubiniStudyProfileInvNormSqFirst

namespace ReciprocityTheory.AnForm.M

open MeasureTheory OnePoint Filter Topology

noncomputable section

def crd0 (x : OnePoint ℂ) : ℂ := x.elim 0 id

def crd1 (x : OnePoint ℂ) : ℂ := x.elim 0 (fun z => z⁻¹)

@[simp] theorem finiteCoord_coe (z : ℂ) : crd0 (z : OnePoint ℂ) = z := rfl
@[simp] theorem finiteCoord_infty : crd0 ∞ = 0 := rfl
@[simp] theorem infiniteCoord_coe (z : ℂ) : crd1 (z : OnePoint ℂ) = z⁻¹ := rfl
@[simp] theorem infiniteCoord_infty : crd1 ∞ = 0 := rfl

theorem continuousOn_finiteCoord : ContinuousOn crd0 (Set.range ((↑) : ℂ → OnePoint ℂ)) := by
  rintro _ ⟨z, rfl⟩
  refine ContinuousAt.continuousWithinAt ?_
  rw [← OnePoint.isOpenEmbedding_coe.continuousAt_iff]
  exact continuousAt_id

theorem continuousOn_infiniteCoord : ContinuousOn crd1 {x | x ≠ ((0 : ℂ) : OnePoint ℂ)} := by
  intro x hx
  refine ContinuousAt.continuousWithinAt ?_
  induction x with
  | infty =>
    show Tendsto crd1 (𝓝 ∞) (𝓝 (crd1 ∞))
    rw [OnePoint.nhds_infty_eq, tendsto_sup, tendsto_map'_iff]
    refine ⟨?_, tendsto_pure_nhds crd1 ∞⟩
    have h : crd1 ∘ ((↑) : ℂ → OnePoint ℂ) = fun z => z⁻¹ := rfl
    rw [h, infiniteCoord_infty, coclosedCompact_eq_cocompact, ← Metric.cobounded_eq_cocompact]
    exact tendsto_inv₀_cobounded
  | coe z =>
    have hz : z ≠ 0 := fun h => hx (by rw [h])
    rw [← OnePoint.isOpenEmbedding_coe.continuousAt_iff]
    exact continuousAt_inv₀ hz

def projectiveLineChartAtZero : OpenPartialHomeomorph (OnePoint ℂ) (Fin 1 → ℂ) where
  toFun x := fun _ => crd0 x
  invFun w := ((w 0 : ℂ) : OnePoint ℂ)
  source := Set.range ((↑) : ℂ → OnePoint ℂ)
  target := Set.univ
  map_source' := by intro x _; exact Set.mem_univ _
  map_target' := by intro w _; exact ⟨w 0, rfl⟩
  left_inv' := by rintro _ ⟨z, rfl⟩; rfl
  right_inv' := by
    intro w _
    funext i
    obtain rfl : i = 0 := Subsingleton.elim _ _
    rfl
  open_source := OnePoint.isOpen_range_coe
  open_target := isOpen_univ
  continuousOn_toFun := continuousOn_pi.2 fun _ => continuousOn_finiteCoord
  continuousOn_invFun := (OnePoint.continuous_coe.comp (continuous_apply 0)).continuousOn

open scoped Classical in

def projectiveLineChartAtInfinity : OpenPartialHomeomorph (OnePoint ℂ) (Fin 1 → ℂ) where
  toFun x := fun _ => crd1 x
  invFun w := if w 0 = 0 then ∞ else (((w 0)⁻¹ : ℂ) : OnePoint ℂ)
  source := {x | x ≠ ((0 : ℂ) : OnePoint ℂ)}
  target := Set.univ
  map_source' := by intro x _; exact Set.mem_univ _
  map_target' := by
    intro w _
    simp only [Set.mem_setOf_eq]
    split_ifs with h
    · exact OnePoint.infty_ne_coe _
    · intro e
      exact h (inv_eq_zero.1 (OnePoint.coe_injective e))
  left_inv' := by
    intro x hx
    induction x with
    | infty => simp
    | coe z =>
      have hz : z ≠ 0 := fun h => hx (by rw [h])
      simp [hz]
  right_inv' := by
    intro w _
    funext i
    obtain rfl : i = 0 := Subsingleton.elim _ _
    by_cases h : w 0 = 0
    · simp [h]
    · simp [h]
  open_source := isOpen_compl_singleton
  open_target := isOpen_univ
  continuousOn_toFun := continuousOn_pi.2 fun _ => continuousOn_infiniteCoord
  continuousOn_invFun := continuous_chart1_inv.continuousOn

theorem projLineChart0_apply (x : OnePoint ℂ) : projectiveLineChartAtZero x = fun _ => crd0 x := rfl
theorem projLineChart1_apply (x : OnePoint ℂ) : projectiveLineChartAtInfinity x = fun _ => crd1 x := rfl
theorem projLineChart0_symm_apply (w : Fin 1 → ℂ) : projectiveLineChartAtZero.symm w = ((w 0 : ℂ) : OnePoint ℂ) := rfl
theorem projLineChart0_source : projectiveLineChartAtZero.source = Set.range ((↑) : ℂ → OnePoint ℂ) := rfl
theorem projLineChart1_source : projectiveLineChartAtInfinity.source = {x | x ≠ ((0 : ℂ) : OnePoint ℂ)} := rfl
theorem projLineChart0_target : projectiveLineChartAtZero.target = Set.univ := rfl
theorem projLineChart1_target : projectiveLineChartAtInfinity.target = Set.univ := rfl

private theorem projLineChart1_symm_of_eq_zero {w : Fin 1 → ℂ} (h : w 0 = 0) : projectiveLineChartAtInfinity.symm w = ∞ := by
  show projectiveLineChartAtInfinity.invFun w = ∞
  dsimp only [projectiveLineChartAtInfinity]
  rw [if_pos h]

private theorem projLineChart1_symm_of_ne_zero {w : Fin 1 → ℂ} (h : w 0 ≠ 0) :
    projectiveLineChartAtInfinity.symm w = (((w 0)⁻¹ : ℂ) : OnePoint ℂ) := by
  show projectiveLineChartAtInfinity.invFun w = _
  dsimp only [projectiveLineChartAtInfinity]
  rw [if_neg h]

@[simp] theorem infiniteCoord_projLineChart1_symm (w : Fin 1 → ℂ) : crd1 (projectiveLineChartAtInfinity.symm w) = w 0 := by
  by_cases h : w 0 = 0
  · rw [projLineChart1_symm_of_eq_zero h, infiniteCoord_infty, h]
  · rw [projLineChart1_symm_of_ne_zero h, infiniteCoord_coe, inv_inv]

@[simp] theorem finiteCoord_projLineChart1_symm (w : Fin 1 → ℂ) : crd0 (projectiveLineChartAtInfinity.symm w) = (w 0)⁻¹ := by
  by_cases h : w 0 = 0
  · rw [projLineChart1_symm_of_eq_zero h, finiteCoord_infty, h, inv_zero]
  · rw [projLineChart1_symm_of_ne_zero h, finiteCoord_coe]

theorem projLineChart1_symm_mem_range {w : Fin 1 → ℂ} :
    projectiveLineChartAtInfinity.symm w ∈ Set.range ((↑) : ℂ → OnePoint ℂ) ↔ w 0 ≠ 0 := by
  by_cases h : w 0 = 0
  · rw [projLineChart1_symm_of_eq_zero h]
    exact ⟨fun ⟨z, hz⟩ => absurd hz (OnePoint.coe_ne_infty z), fun h' => absurd h h'⟩
  · rw [projLineChart1_symm_of_ne_zero h]
    exact ⟨fun _ => h, fun _ => ⟨_, rfl⟩⟩

theorem projLineChart0_symm_ne_zero {w : Fin 1 → ℂ} :
    projectiveLineChartAtZero.symm w ≠ ((0 : ℂ) : OnePoint ℂ) ↔ w 0 ≠ 0 := by
  rw [projLineChart0_symm_apply]
  exact ⟨fun h h' => h (by rw [h']), fun h h' => h (OnePoint.coe_injective h')⟩

def p1 : FinHolAtlas 1 (OnePoint ℂ) where
  n := 2
  chart := ![projectiveLineChartAtZero, projectiveLineChartAtInfinity]
  cover := by
    intro x
    induction x with
    | infty => exact ⟨1, show ∞ ∈ projectiveLineChartAtInfinity.source from OnePoint.infty_ne_coe 0⟩
    | coe z => exact ⟨0, show (z : OnePoint ℂ) ∈ projectiveLineChartAtZero.source from ⟨z, rfl⟩⟩
  holo := by
    refine Fin.forall_fin_two.2 ⟨Fin.forall_fin_two.2 ⟨?_, ?_⟩, Fin.forall_fin_two.2 ⟨?_, ?_⟩⟩
    · show AnalyticOnNhd ℂ (projectiveLineChartAtZero ∘ projectiveLineChartAtZero.symm) _
      have e : (projectiveLineChartAtZero ∘ projectiveLineChartAtZero.symm) = fun w : Fin 1 → ℂ => fun _ : Fin 1 => w 0 := by
        funext w i; rfl
      rw [e]
      exact fun w _ => projLine_analyticAt_const_apply_zero w
    · show AnalyticOnNhd ℂ (projectiveLineChartAtInfinity ∘ projectiveLineChartAtZero.symm)
        (projectiveLineChartAtZero.target ∩ projectiveLineChartAtZero.symm ⁻¹' projectiveLineChartAtInfinity.source)
      have e : (projectiveLineChartAtInfinity ∘ projectiveLineChartAtZero.symm) = fun w : Fin 1 → ℂ => fun _ : Fin 1 => (w 0)⁻¹ := by
        funext w i; rfl
      rw [e]
      exact fun w hw => projLine_analyticAt_const_inv_apply_zero (projLineChart0_symm_ne_zero.1 hw.2)
    · show AnalyticOnNhd ℂ (projectiveLineChartAtZero ∘ projectiveLineChartAtInfinity.symm)
        (projectiveLineChartAtInfinity.target ∩ projectiveLineChartAtInfinity.symm ⁻¹' projectiveLineChartAtZero.source)
      have e : (projectiveLineChartAtZero ∘ projectiveLineChartAtInfinity.symm) = fun w : Fin 1 → ℂ => fun _ : Fin 1 => (w 0)⁻¹ := by
        funext w i; simp only [Function.comp_apply, projLineChart0_apply, finiteCoord_projLineChart1_symm]
      rw [e]
      exact fun w hw => projLine_analyticAt_const_inv_apply_zero (projLineChart1_symm_mem_range.1 hw.2)
    · show AnalyticOnNhd ℂ (projectiveLineChartAtInfinity ∘ projectiveLineChartAtInfinity.symm) _
      have e : (projectiveLineChartAtInfinity ∘ projectiveLineChartAtInfinity.symm) = fun w : Fin 1 → ℂ => fun _ : Fin 1 => w 0 := by
        funext w i; simp only [Function.comp_apply, projLineChart1_apply, infiniteCoord_projLineChart1_symm]
      rw [e]
      exact fun w _ => projLine_analyticAt_const_apply_zero w

theorem projLineAtlas_n : p1.n = 2 := rfl
theorem projLineAtlas_chart0 : p1.chart (0 : Fin 2) = projectiveLineChartAtZero := rfl
theorem projLineAtlas_chart1 : p1.chart (1 : Fin 2) = projectiveLineChartAtInfinity := rfl

open scoped Classical in

def fsPot : LocPot (OnePoint ℂ) where
  U x := if x = ∞ then projectiveLineChartAtInfinity.source else projectiveLineChartAtZero.source
  isOpen_U := by
    intro x
    split_ifs
    · exact projectiveLineChartAtInfinity.open_source
    · exact projectiveLineChartAtZero.open_source
  mem_U := by
    intro x
    split_ifs with h
    · subst h; exact OnePoint.infty_ne_coe 0
    · obtain ⟨z, rfl⟩ := OnePoint.ne_infty_iff_exists.1 h
      exact ⟨z, rfl⟩
  φ x y := if x = ∞ then (1 / 2) * Real.log (1 + ‖crd1 y‖ ^ 2)
    else (1 / 2) * Real.log (1 + ‖crd0 y‖ ^ 2)

theorem fsPot_U_infty : fsPot.U ∞ = projectiveLineChartAtInfinity.source := by simp [fsPot]
theorem fsPot_U_coe (z : ℂ) : fsPot.U (z : OnePoint ℂ) = projectiveLineChartAtZero.source := by simp [fsPot]
theorem fsPot_φ_infty : fsPot.φ ∞ = fun y => (1 / 2) * Real.log (1 + ‖crd1 y‖ ^ 2) := by simp [fsPot]
theorem fsPot_φ_coe (z : ℂ) :
    fsPot.φ (z : OnePoint ℂ) = fun y => (1 / 2) * Real.log (1 + ‖crd0 y‖ ^ 2) := by simp [fsPot]

open scoped Classical in

def projectiveLinePairSection (x y : OnePoint ℂ) : ℂ := if x = ∞ then crd1 y else 1

theorem projLineSection_infty : projectiveLinePairSection ∞ = crd1 := by
  funext y
  simp [projectiveLinePairSection]
theorem projLineSection_coe (z : ℂ) : projectiveLinePairSection (z : OnePoint ℂ) = fun _ => 1 := by
  funext y
  simp [projectiveLinePairSection]

theorem fsPot_chart (x : OnePoint ℂ) : ∀ j : Fin 2,
    (fsPot.φ x ∘ (p1.chart j).symm = fun w => fubiniStudyProfile (fsQ w)) ∨
      ((fsPot.φ x ∘ (p1.chart j).symm = fun w => fubiniStudyProfileInv (fsQ w)) ∧
        ∀ w ∈ (p1.chart j).target ∩ (p1.chart j).symm ⁻¹' fsPot.U x, w 0 ≠ 0) := by
  intro j
  revert j
  refine Fin.forall_fin_two.2 ⟨?_, ?_⟩
  · induction x with
    | infty =>
      right
      refine ⟨?_, fun w hw => projLineChart0_symm_ne_zero.1 (by rw [fsPot_U_infty] at hw; exact hw.2)⟩
      funext w
      rw [fsPot_φ_infty, projLineAtlas_chart0]
      simp only [Function.comp_apply, projLineChart0_symm_apply, infiniteCoord_coe, fubiniStudyProfileInv, fsQ, norm_inv, inv_pow]
    | coe z =>
      left
      funext w
      rw [fsPot_φ_coe, projLineAtlas_chart0]
      simp only [Function.comp_apply, projLineChart0_symm_apply, finiteCoord_coe, fubiniStudyProfile, fsQ]
  · induction x with
    | infty =>
      left
      funext w
      rw [fsPot_φ_infty, projLineAtlas_chart1]
      simp only [Function.comp_apply, infiniteCoord_projLineChart1_symm, fubiniStudyProfile, fsQ]
    | coe z =>
      right
      refine ⟨?_, fun w hw => projLineChart1_symm_mem_range.1 (by rw [fsPot_U_coe] at hw; exact hw.2)⟩
      funext w
      rw [fsPot_φ_coe, projLineAtlas_chart1]
      simp only [Function.comp_apply, finiteCoord_projLineChart1_symm, fubiniStudyProfileInv, fsQ, norm_inv, inv_pow]

theorem fsPot_smooth (x : OnePoint ℂ) : p1.SmoothOn (fsPot.U x) (fsPot.φ x) := by
  intro j
  rcases fsPot_chart x j with h | ⟨h, hne⟩
  · rw [h]
    exact contDiff_fubiniStudyProfile_normSqFirst.contDiffOn
  · rw [h]
    exact contDiffOn_fubiniStudyProfileInv_normSqFirst.mono fun w hw => hne w hw

theorem holomorphicOn_infiniteCoord : p1.HoloOn {x | x ≠ ((0 : ℂ) : OnePoint ℂ)} crd1 := by
  refine Fin.forall_fin_two.2 ⟨?_, ?_⟩
  · intro w hw
    have e : crd1 ∘ (p1.chart (0 : Fin 2)).symm = fun v : Fin 1 → ℂ => (v 0)⁻¹ := by
      funext v
      rfl
    rw [e]
    exact projLine_analyticAt_inv_apply_zero (projLineChart0_symm_ne_zero.1 hw.2)
  · intro w _
    have e : crd1 ∘ (p1.chart (1 : Fin 2)).symm = fun v : Fin 1 → ℂ => v 0 := by
      funext v
      exact infiniteCoord_projLineChart1_symm v
    rw [e]
    exact projLine_analyticAt_apply_zero w

theorem holomorphicOn_finiteCoord : p1.HoloOn (Set.range ((↑) : ℂ → OnePoint ℂ)) crd0 := by
  refine Fin.forall_fin_two.2 ⟨?_, ?_⟩
  · intro w _
    exact projLine_analyticAt_apply_zero w
  · intro w hw
    have e : crd0 ∘ (p1.chart (1 : Fin 2)).symm = fun v : Fin 1 → ℂ => (v 0)⁻¹ := by
      funext v
      exact finiteCoord_projLineChart1_symm v
    rw [e]
    exact projLine_analyticAt_inv_apply_zero (projLineChart1_symm_mem_range.1 hw.2)

theorem holoOn_mono {U V : Set (OnePoint ℂ)} {g : OnePoint ℂ → ℂ} (h : p1.HoloOn U g)
    (hVU : V ⊆ U) : p1.HoloOn V g := by
  intro j w hw
  exact h j w ⟨hw.1, hVU hw.2⟩

theorem holoOn_const (U : Set (OnePoint ℂ)) (c : ℂ) : p1.HoloOn U (fun _ => c) := by
  intro j w _
  exact analyticAt_const

theorem holomorphicOn_comp_finiteCoord {B : Set ℂ} {F : ℂ → ℂ} (hF : AnalyticOnNhd ℂ F B) :
    p1.HoloOn (projectiveLineChartAtZero.source ∩ projectiveLineChartAtZero ⁻¹' {w | w 0 ∈ B}) (fun x => F (crd0 x)) := by
  refine Fin.forall_fin_two.2 ⟨?_, ?_⟩
  · intro w hw
    have hB : w 0 ∈ B := hw.2.2
    have h := AnalyticAt.comp (g := F) (f := fun v : Fin 1 → ℂ => v 0) (x := w) (hF (w 0) hB)
      (projLine_analyticAt_apply_zero w)
    exact h
  · intro w hw
    have hne : w 0 ≠ 0 := projLineChart1_symm_mem_range.1 hw.2.1
    have hB : (w 0)⁻¹ ∈ B := by
      have h2 : crd0 (projectiveLineChartAtInfinity.symm w) ∈ B := hw.2.2
      rwa [finiteCoord_projLineChart1_symm] at h2
    have e : (fun x => F (crd0 x)) ∘ (p1.chart (1 : Fin 2)).symm =
        F ∘ (fun v : Fin 1 → ℂ => (v 0)⁻¹) := by
      funext v
      exact congrArg F (finiteCoord_projLineChart1_symm v)
    rw [e]
    have h := AnalyticAt.comp (g := F) (f := fun v : Fin 1 → ℂ => (v 0)⁻¹) (x := w) (hF _ hB)
      (projLine_analyticAt_inv_apply_zero hne)
    exact h

theorem fs_local (ζ0 : ℂ) (h0 : ζ0 ≠ 0) : ∃ W : Set (OnePoint ℂ), IsOpen W ∧
    (ζ0 : OnePoint ℂ) ∈ W ∧ ∃ G : OnePoint ℂ → ℂ, p1.HoloOn W G ∧
      ∀ z ∈ W, ∃ ζ : ℂ, z = ζ ∧ ζ ≠ 0 ∧ (G z).re = Real.log ‖ζ‖ := by
  set B : Set ℂ := {ζ | ζ * ζ0⁻¹ ∈ Complex.slitPlane} with hBdef
  have hBo : IsOpen B := Complex.isOpen_slitPlane.preimage (continuous_id.mul continuous_const)
  have hF : AnalyticOnNhd ℂ (fun ζ : ℂ => Complex.log (ζ * ζ0⁻¹) + (Real.log ‖ζ0‖ : ℂ)) B := by
    intro ζ hζ
    exact ((analyticAt_id.mul analyticAt_const).clog hζ).add analyticAt_const
  refine ⟨projectiveLineChartAtZero.source ∩ projectiveLineChartAtZero ⁻¹' {w | w 0 ∈ B},
    projectiveLineChartAtZero.isOpen_inter_preimage (hBo.preimage (continuous_apply 0)), ⟨⟨ζ0, rfl⟩, ?_⟩, _,
    holomorphicOn_comp_finiteCoord hF, ?_⟩
  · show ζ0 * ζ0⁻¹ ∈ Complex.slitPlane
    rw [mul_inv_cancel₀ h0]
    exact Complex.one_mem_slitPlane
  · rintro z ⟨⟨ζ, rfl⟩, hz⟩
    have hζB : ζ * ζ0⁻¹ ∈ Complex.slitPlane := hz
    have hne : ζ * ζ0⁻¹ ≠ 0 := Complex.slitPlane_ne_zero hζB
    have hζ : ζ ≠ 0 := left_ne_zero_of_mul hne
    refine ⟨ζ, rfl, hζ, ?_⟩
    show (Complex.log (crd0 (ζ : OnePoint ℂ) * ζ0⁻¹) + (Real.log ‖ζ0‖ : ℂ)).re = Real.log ‖ζ‖
    rw [finiteCoord_coe, Complex.add_re, Complex.log_re, Complex.ofReal_re, norm_mul, norm_inv,
      Real.log_mul (norm_ne_zero_iff.2 hζ) (inv_ne_zero (norm_ne_zero_iff.2 h0)), Real.log_inv]
    ring

private theorem half_log_one_add_inv_sq_sub_eq_neg_log {ζ : ℂ} (h : ζ ≠ 0) :
    (1 / 2) * Real.log (1 + ‖ζ⁻¹‖ ^ 2) - (1 / 2) * Real.log (1 + ‖ζ‖ ^ 2) = -Real.log ‖ζ‖ := by
  have hn : 0 < ‖ζ‖ := norm_pos_iff.2 h
  have hn2 : ‖ζ‖ ^ 2 ≠ 0 := by positivity
  have h1 : 1 + ‖ζ⁻¹‖ ^ 2 = (1 + ‖ζ‖ ^ 2) / ‖ζ‖ ^ 2 := by
    rw [norm_inv, inv_pow, add_div, div_self hn2, one_div, add_comm]
  rw [h1, Real.log_div (by positivity) hn2, Real.log_pow]
  push_cast
  ring

theorem projLine_isSmoothPotential : IsPotential p1 fsPot := by
  refine ⟨fsPot_smooth, ?_⟩
  intro x x' y hy
  induction x with
  | infty =>
    induction x' with
    | infty =>
      exact ⟨Set.univ, isOpen_univ, trivial, fun _ => 0, holoOn_const _ 0, fun z _ => by simp⟩
    | coe z' =>
      obtain ⟨hy1, hy2⟩ := hy
      rw [fsPot_U_infty] at hy1
      rw [fsPot_U_coe] at hy2
      obtain ⟨ζ0, rfl⟩ := hy2
      have h0 : ζ0 ≠ 0 := fun h => hy1 (by rw [h])
      obtain ⟨W, hWo, hyW, G, hG, hGW⟩ := fs_local ζ0 h0
      refine ⟨W, hWo, hyW, fun z => -G z, fun j w hw => (hG j w hw).neg, ?_⟩
      rintro z ⟨⟨hzW, _⟩, _⟩
      obtain ⟨ζ, rfl, hζ, hre⟩ := hGW z hzW
      rw [fsPot_φ_infty, fsPot_φ_coe]
      simp only [infiniteCoord_coe, finiteCoord_coe, Complex.neg_re, hre]
      exact half_log_one_add_inv_sq_sub_eq_neg_log hζ
  | coe z =>
    induction x' with
    | infty =>
      obtain ⟨hy1, hy2⟩ := hy
      rw [fsPot_U_coe] at hy1
      rw [fsPot_U_infty] at hy2
      obtain ⟨ζ0, rfl⟩ := hy1
      have h0 : ζ0 ≠ 0 := fun h => hy2 (by rw [h])
      obtain ⟨W, hWo, hyW, G, hG, hGW⟩ := fs_local ζ0 h0
      refine ⟨W, hWo, hyW, G, hG, ?_⟩
      rintro z ⟨⟨hzW, _⟩, _⟩
      obtain ⟨ζ, rfl, hζ, hre⟩ := hGW z hzW
      rw [fsPot_φ_infty, fsPot_φ_coe]
      simp only [infiniteCoord_coe, finiteCoord_coe, hre]
      linarith [half_log_one_add_inv_sq_sub_eq_neg_log hζ]
    | coe z'' =>
      exact ⟨Set.univ, isOpen_univ, trivial, fun _ => 0, holoOn_const _ 0, fun w _ => by
        simp [fsPot_φ_coe]⟩

theorem projLine_isPlurisubharmonic : IsPsh p1 fsPot := by
  intro x j y hy v
  rcases fsPot_chart x j with h | ⟨h, hne⟩
  · rw [h]
    have ht : 0 ≤ ‖y 0‖ ^ 2 := by positivity
    have hG : ∀ᶠ t in 𝓝 (‖y 0‖ ^ 2), HasDerivAt fubiniStudyProfile ((1 / 2) * (1 + t)⁻¹) t :=
      (lt_mem_nhds (by linarith : (-1 : ℝ) < ‖y 0‖ ^ 2)).mono fun t ht' => hasDerivAt_fubiniStudyProfile ht'
    have hG' := (((hasDerivAt_id' (‖y 0‖ ^ 2)).const_add 1).inv
      (by positivity : (1 : ℝ) + ‖y 0‖ ^ 2 ≠ 0)).const_mul (1 / 2 : ℝ)
    rw [projLine_leviForm_radial (F := fun w => fubiniStudyProfile (fsQ w)) (Filter.Eventually.of_forall fun w => rfl) hG hG' v]
    refine mul_nonneg ?_ (by positivity)
    have h1 : (0 : ℝ) < 1 + ‖y 0‖ ^ 2 := by positivity
    beta_reduce
    generalize ‖y 0‖ ^ 2 = t at ht h1 ⊢
    have key : 1 / 2 * (-1 / (1 + t) ^ 2) * t + 1 / 2 * (1 + t)⁻¹ = 1 / (2 * (1 + t) ^ 2) := by
      field_simp
      ring
    have hpos : 0 ≤ 1 / (2 * (1 + t) ^ 2) := by positivity
    linarith [key, hpos]
  · rw [h]
    have ht : 0 < ‖y 0‖ ^ 2 := pow_pos (norm_pos_iff.2 (hne y hy)) 2
    have hG : ∀ᶠ t in 𝓝 (‖y 0‖ ^ 2), HasDerivAt fubiniStudyProfileInv (-(1 / 2) * (t * (t + 1))⁻¹) t :=
      (lt_mem_nhds ht).mono fun t ht' => hasDerivAt_fubiniStudyProfileInv ht'
    have hG' := (((hasDerivAt_id' (‖y 0‖ ^ 2)).mul ((hasDerivAt_id' (‖y 0‖ ^ 2)).add_const 1)).inv
      (by positivity : ‖y 0‖ ^ 2 * (‖y 0‖ ^ 2 + 1) ≠ 0)).const_mul (-(1 / 2) : ℝ)
    rw [projLine_leviForm_radial (F := fun w => fubiniStudyProfileInv (fsQ w)) (Filter.Eventually.of_forall fun w => rfl) hG hG' v]
    refine mul_nonneg ?_ (by positivity)
    simp only [Pi.mul_apply]
    beta_reduce
    generalize ‖y 0‖ ^ 2 = t at ht ⊢
    have ht0 : t ≠ 0 := ht.ne'
    have ht1 : t + 1 ≠ 0 := by positivity
    have hu : t * (t + 1) * (t * (t + 1))⁻¹ = 1 := mul_inv_cancel₀ (mul_ne_zero ht0 ht1)
    have hpos : 0 ≤ 1 / 2 * (t * (t * (t + 1))⁻¹) ^ 2 := by positivity
    have hv : (t * (t + 1)) ^ 2 * ((t * (t + 1)) ^ 2)⁻¹ = 1 :=
      mul_inv_cancel₀ (pow_ne_zero 2 (mul_ne_zero ht0 ht1))
    refine le_of_le_of_eq hpos ?_
    linear_combination (1 / 2 * (2 * t + 1) * t * ((t * (t + 1)) ^ 2)⁻¹ *
        (1 + t * (t + 1) * (t * (t + 1))⁻¹) - 1 / 2 * (t * (t + 1))⁻¹) * hu +
      (-(1 / 2) * (2 * t + 1) * t * ((t * (t + 1))⁻¹) ^ 2) * hv

def fsH (x : OnePoint ℂ) : ℝ := x.elim 1 (fun z => ‖z‖ ^ 2 / (1 + ‖z‖ ^ 2))

theorem fsH_chart0 : fsH ∘ projectiveLineChartAtZero.symm = fun w => fsQ w / (1 + fsQ w) := rfl

theorem fsH_chart1 : fsH ∘ projectiveLineChartAtInfinity.symm = fun w => 1 / (1 + fsQ w) := by
  funext w
  simp only [Function.comp_apply]
  by_cases h : w 0 = 0
  · rw [projLineChart1_symm_of_eq_zero h]
    show (1 : ℝ) = 1 / (1 + ‖w 0‖ ^ 2)
    rw [h]
    simp
  · rw [projLineChart1_symm_of_ne_zero h]
    have hn : ‖w 0‖ ≠ 0 := norm_ne_zero_iff.2 h
    show ‖(w 0)⁻¹‖ ^ 2 / (1 + ‖(w 0)⁻¹‖ ^ 2) = 1 / (1 + ‖w 0‖ ^ 2)
    rw [norm_inv, inv_pow]
    field_simp
    ring

theorem projLine_smooth_of_charts {f : OnePoint ℂ → ℝ}
    (h0 : ContDiff ℝ (⊤ : ℕ∞) (f ∘ projectiveLineChartAtZero.symm)) (h1 : ContDiff ℝ (⊤ : ℕ∞) (f ∘ projectiveLineChartAtInfinity.symm)) :
    p1.Smooth f := by
  refine Fin.forall_fin_two.2 ⟨?_, ?_⟩
  · exact h0.contDiffOn
  · exact h1.contDiffOn

private theorem contDiff_fsQ' : ContDiff ℝ (⊤ : ℕ∞) fsQ :=
  (contDiff_norm_sq ℂ).comp (contDiff_apply ℝ ℂ (0 : Fin 1))

theorem contDiff_fubiniStudyRatio_comp_chart0 : ContDiff ℝ (⊤ : ℕ∞) (fsH ∘ projectiveLineChartAtZero.symm) := by
  rw [fsH_chart0]
  exact contDiff_fsQ'.div (contDiff_const.add contDiff_fsQ') fun w => by
    simp only [fsQ]
    positivity

theorem contDiff_fubiniStudyRatio_comp_chart1 : ContDiff ℝ (⊤ : ℕ∞) (fsH ∘ projectiveLineChartAtInfinity.symm) := by
  rw [fsH_chart1]
  exact contDiff_const.div (contDiff_const.add contDiff_fsQ') fun w => by
    simp only [fsQ]
    positivity

def fsχ1 (x : OnePoint ℂ) : ℝ := Real.smoothTransition (4 * fsH x - 1)

theorem smooth_fsχ1 : p1.Smooth fsχ1 := by
  refine projLine_smooth_of_charts ?_ ?_
  · have h := Real.smoothTransition.contDiff.comp (((contDiff_const (c := (4 : ℝ))).mul contDiff_fubiniStudyRatio_comp_chart0).sub
      (contDiff_const : ContDiff ℝ (⊤ : ℕ∞) fun _ : Fin 1 → ℂ => (1 : ℝ)))
    exact h
  · have h := Real.smoothTransition.contDiff.comp (((contDiff_const (c := (4 : ℝ))).mul contDiff_fubiniStudyRatio_comp_chart1).sub
      (contDiff_const : ContDiff ℝ (⊤ : ℕ∞) fun _ : Fin 1 → ℂ => (1 : ℝ)))
    exact h

theorem smooth_one_sub_fsχ1 : p1.Smooth (fun x => 1 - fsχ1 x) := by
  intro j
  have h := (contDiffOn_const (c := (1 : ℝ))).sub (smooth_fsχ1 j)
  exact h

private theorem fsH_eq_one_div_one_add_norm_sq_of_ne_zero {x : OnePoint ℂ} (hx : x ≠ ((0 : ℂ) : OnePoint ℂ)) :
    fsH x = 1 / (1 + ‖crd1 x‖ ^ 2) := by
  induction x with
  | infty =>
    show (1 : ℝ) = 1 / (1 + ‖crd1 ∞‖ ^ 2)
    simp
  | coe z =>
    have hz : z ≠ 0 := fun h => hx (by rw [h])
    have hn : ‖z‖ ≠ 0 := norm_ne_zero_iff.2 hz
    show ‖z‖ ^ 2 / (1 + ‖z‖ ^ 2) = 1 / (1 + ‖z⁻¹‖ ^ 2)
    rw [norm_inv, inv_pow]
    field_simp
    ring

theorem continuous_fsH : Continuous fsH := by
  refine continuous_iff_continuousAt.2 fun x => ?_
  induction x with
  | infty =>
    have hU : {x : OnePoint ℂ | x ≠ ((0 : ℂ) : OnePoint ℂ)} ∈ 𝓝 (∞ : OnePoint ℂ) :=
      isOpen_compl_singleton.mem_nhds (OnePoint.infty_ne_coe 0)
    have hc : ContinuousAt crd1 ∞ :=
      (continuousOn_infiniteCoord ∞ (OnePoint.infty_ne_coe 0)).continuousAt hU
    refine ContinuousAt.congr (f := fun x => 1 / (1 + ‖crd1 x‖ ^ 2)) ?_ ?_
    · exact continuousAt_const.div (continuousAt_const.add (hc.norm.pow 2)) (by positivity)
    · filter_upwards [hU] with x hx using (fsH_eq_one_div_one_add_norm_sq_of_ne_zero hx).symm
  | coe z =>
    have hU : Set.range ((↑) : ℂ → OnePoint ℂ) ∈ 𝓝 (z : OnePoint ℂ) :=
      OnePoint.isOpen_range_coe.mem_nhds ⟨z, rfl⟩
    have hc : ContinuousAt crd0 z := (continuousOn_finiteCoord _ ⟨z, rfl⟩).continuousAt hU
    refine ContinuousAt.congr (f := fun x => ‖crd0 x‖ ^ 2 / (1 + ‖crd0 x‖ ^ 2)) ?_ ?_
    · exact (hc.norm.pow 2).div (continuousAt_const.add (hc.norm.pow 2)) (by positivity)
    · filter_upwards [hU] with x hx
      obtain ⟨w, rfl⟩ := hx
      rfl

def projLinePartition : ChartPartition p1 where
  χ := ![fun x => 1 - fsχ1 x, fsχ1]
  smooth := by
    refine Fin.forall_fin_two.2 ⟨?_, ?_⟩
    · exact smooth_one_sub_fsχ1
    · exact smooth_fsχ1
  nonneg := by
    refine Fin.forall_fin_two.2 ⟨?_, ?_⟩
    · intro x
      show 0 ≤ 1 - fsχ1 x
      exact sub_nonneg.2 (Real.smoothTransition.le_one _)
    · intro x
      exact Real.smoothTransition.nonneg _
  tsupport_subset := by
    refine Fin.forall_fin_two.2 ⟨?_, ?_⟩
    · show tsupport (fun x => 1 - fsχ1 x) ⊆ projectiveLineChartAtZero.source
      have hsub : tsupport (fun x => 1 - fsχ1 x) ⊆ {x | fsH x ≤ 1 / 2} := by
        refine closure_minimal ?_ (isClosed_le continuous_fsH continuous_const)
        intro x hx
        by_contra hc
        apply hx
        simp only [Set.mem_setOf_eq, not_le] at hc
        show 1 - Real.smoothTransition (4 * fsH x - 1) = 0
        rw [Real.smoothTransition.one_of_one_le (by linarith)]
        ring
      intro x hx
      have := hsub hx
      induction x with
      | infty =>
        simp only [Set.mem_setOf_eq] at this
        norm_num [fsH] at this
      | coe z => exact ⟨z, rfl⟩
    · show tsupport fsχ1 ⊆ projectiveLineChartAtInfinity.source
      have hsub : tsupport fsχ1 ⊆ {x | 1 / 4 ≤ fsH x} := by
        refine closure_minimal ?_ (isClosed_le continuous_const continuous_fsH)
        intro x hx
        by_contra hc
        apply hx
        simp only [Set.mem_setOf_eq, not_le] at hc
        exact Real.smoothTransition.zero_of_nonpos (by linarith)
      intro x hx h0
      have := hsub hx
      rw [h0] at this
      norm_num [fsH] at this
  sum_eq_one := by
    intro x
    show ∑ j : Fin 2, ![fun x => 1 - fsχ1 x, fsχ1] j x = 1
    simp [Fin.sum_univ_two]

theorem projLine_partition : Nonempty (ChartPartition p1) := ⟨projLinePartition⟩

private theorem norm_inv_mul_exp_half_log_eq_of_ne_zero {ζ : ℂ} (h : ζ ≠ 0) :
    ‖ζ⁻¹‖ * Real.exp (-((1 / 2) * Real.log (1 + ‖ζ⁻¹‖ ^ 2))) =
      ‖(1 : ℂ)‖ * Real.exp (-((1 / 2) * Real.log (1 + ‖ζ‖ ^ 2))) := by
  have hn : ‖ζ‖ ≠ 0 := norm_ne_zero_iff.2 h
  have e := half_log_one_add_inv_sq_sub_eq_neg_log h
  have e2 : -((1 / 2) * Real.log (1 + ‖ζ⁻¹‖ ^ 2)) =
      -((1 / 2) * Real.log (1 + ‖ζ‖ ^ 2)) + Real.log ‖ζ‖ := by linarith
  rw [e2, Real.exp_add, Real.exp_log (norm_pos_iff.2 h), norm_inv, norm_one,
    mul_comm (Real.exp _) ‖ζ‖, ← mul_assoc, inv_mul_cancel₀ hn]

theorem projLine_isHolomorphicSection : IsSection p1 fsPot projectiveLinePairSection := by
  refine ⟨fun x => ?_, ?_⟩
  · induction x with
    | infty =>
      rw [projLineSection_infty, fsPot_U_infty]
      exact holomorphicOn_infiniteCoord
    | coe z =>
      rw [projLineSection_coe, fsPot_U_coe]
      exact holoOn_const _ 1
  · intro x x' y hy
    induction x with
    | infty =>
      induction x' with
      | infty => rfl
      | coe z' =>
        obtain ⟨hy1, hy2⟩ := hy
        rw [fsPot_U_infty] at hy1
        rw [fsPot_U_coe] at hy2
        obtain ⟨ζ, rfl⟩ := hy2
        have hζ : ζ ≠ 0 := fun h => hy1 (by rw [h])
        rw [projLineSection_infty, projLineSection_coe, fsPot_φ_infty, fsPot_φ_coe]
        exact norm_inv_mul_exp_half_log_eq_of_ne_zero hζ
    | coe z =>
      induction x' with
      | infty =>
        obtain ⟨hy1, hy2⟩ := hy
        rw [fsPot_U_coe] at hy1
        rw [fsPot_U_infty] at hy2
        obtain ⟨ζ, rfl⟩ := hy1
        have hζ : ζ ≠ 0 := fun h => hy2 (by rw [h])
        rw [projLineSection_infty, projLineSection_coe, fsPot_φ_infty, fsPot_φ_coe]
        exact (norm_inv_mul_exp_half_log_eq_of_ne_zero hζ).symm
      | coe z'' =>
        rw [projLineSection_coe, projLineSection_coe, fsPot_φ_coe, fsPot_φ_coe]

theorem projLine_isCompatibleChart (k : Fin 2) : IsCompatChart p1 (p1.chart k) := by
  intro j
  exact ⟨p1.holo j k, p1.holo k j⟩

theorem projLine_isSimpleNormalCrossing : IsSNC p1 fsPot projectiveLinePairSection ![1] ![{∞}] := by
  intro x
  induction x with
  | infty =>
    refine ⟨projectiveLineChartAtInfinity, projLine_isCompatibleChart 1, OnePoint.infty_ne_coe 0, fun y hy => by rw [fsPot_U_infty]; exact hy,
      fun _ => Option.some 0, ?_, ?_, fun _ => 1, holoOn_const _ 1, fun _ _ => one_ne_zero, ?_⟩
    · intro k k' i _ _
      exact Subsingleton.elim k k'
    · intro k
      obtain rfl : k = 0 := Subsingleton.elim _ _
      ext y
      constructor
      · rintro ⟨hy1, hy2⟩
        have hy : y = ∞ := hy1
        subst hy
        exact ⟨hy2, 0, rfl, rfl⟩
      · rintro ⟨hy1, i, _, hi⟩
        refine ⟨?_, hy1⟩
        induction y with
        | infty => exact Set.mem_singleton _
        | coe z =>
          have hz : z⁻¹ = 0 := hi
          exact absurd (show (z : OnePoint ℂ) = ((0 : ℂ) : OnePoint ℂ) by rw [inv_eq_zero.1 hz]) hy1
    · intro y _
      rw [projLineSection_infty, Fin.prod_univ_one]
      show crd1 y = 1 * crd1 y ^ 1
      ring
  | coe z =>
    refine ⟨projectiveLineChartAtZero, projLine_isCompatibleChart 0, ⟨z, rfl⟩, fun y hy => by rw [fsPot_U_coe]; exact hy,
      fun _ => Option.none, ?_, ?_, fun _ => 1, holoOn_const _ 1, fun _ _ => one_ne_zero, ?_⟩
    · intro k k' i hk _
      cases hk
    · intro k
      obtain rfl : k = 0 := Subsingleton.elim _ _
      ext y
      constructor
      · rintro ⟨hy1, ⟨w, rfl⟩⟩
        exact absurd (hy1 : (w : OnePoint ℂ) = ∞) (OnePoint.coe_ne_infty w)
      · rintro ⟨_, i, hi, _⟩
        cases hi
    · intro y _
      rw [projLineSection_coe, Fin.prod_univ_one]
      show (1 : ℂ) = 1 * 1
      ring

def ptAtlas (Y : Type*) [TopologicalSpace Y] [Unique Y] : FinHolAtlas 0 Y where
  n := 1
  chart _ :=
    { toFun := fun _ => 0
      invFun := fun _ => default
      source := Set.univ
      target := Set.univ
      map_source' := by intro x _; exact Set.mem_univ _
      map_target' := by intro x _; exact Set.mem_univ _
      left_inv' := by intro x _; exact Subsingleton.elim _ _
      right_inv' := by intro x _; exact Subsingleton.elim _ _
      open_source := isOpen_univ
      open_target := isOpen_univ
      continuousOn_toFun := continuousOn_const
      continuousOn_invFun := continuousOn_const }
  cover := fun _ => ⟨0, Set.mem_univ _⟩
  holo := fun _ _ _ _ => analyticAt_const

def ptPart (Y : Type*) [TopologicalSpace Y] [Unique Y] : ChartPartition (ptAtlas Y) where
  χ _ _ := 1
  smooth _ _ := contDiffOn_const
  nonneg _ _ := zero_le_one
  tsupport_subset _ := Set.subset_univ _
  sum_eq_one _ := by
    show ∑ _j : Fin 1, (1 : ℝ) = 1
    simp

theorem ptAtlas_mInt (Y : Type*) [TopologicalSpace Y] [Unique Y] (g : Y → ℝ) :
    mInt (ptAtlas Y) Fin.elim0 g = g default := by
  have hne : Nonempty (ChartPartition (ptAtlas Y)) := ⟨ptPart Y⟩
  have hχ : ∀ (Q : ChartPartition (ptAtlas Y)) (x : Y), Q.χ (0 : Fin 1) x = 1 := by
    intro Q x
    have h := Q.sum_eq_one x
    change ∑ j : Fin 1, Q.χ j x = 1 at h
    rwa [Fin.sum_univ_one] at h
  have hd : ∀ y : Fin 0 → ℂ, locDens (ptAtlas Y) Fin.elim0 (0 : Fin 1) y = 1 := by
    intro y
    simp [locDens, maDens, mdisc]
  have ht : ((ptAtlas Y).chart (0 : Fin 1)).target = Set.univ := rfl
  unfold mInt
  rw [dif_pos hne]
  unfold integralWith
  change ∑ j : Fin 1, _ = _
  rw [Fin.sum_univ_one]
  have e : ∀ y : Fin 0 → ℂ, hne.some.χ (0 : Fin 1) (((ptAtlas Y).chart (0 : Fin 1)).symm y) *
      g (((ptAtlas Y).chart (0 : Fin 1)).symm y) * locDens (ptAtlas Y) Fin.elim0 (0 : Fin 1) y =
      g default := by
    intro y
    rw [hχ, hd, Subsingleton.elim (((ptAtlas Y).chart (0 : Fin 1)).symm y) default]
    ring
  simp only [e, ht]
  simp [MeasureTheory.volume_pi, MeasureTheory.Measure.pi_univ, MeasureTheory.measureReal_def]

end

end ReciprocityTheory.AnForm.M
