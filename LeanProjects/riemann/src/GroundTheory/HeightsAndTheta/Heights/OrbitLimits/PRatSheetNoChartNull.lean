import Mathlib
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StRatSheetNoChartNull
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PSheetOnlyNull
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PFiniteMapOpen
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PCriticalImageNull
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Filter Topology Matrix ComplexSets

noncomputable section

namespace RatSheetNoChartNull

variable {n d : ℕ}

theorem continuousOn_ratMap (p : Fin d → MvPolynomial (Fin n) ℂ) (q : MvPolynomial (Fin n) ℂ) :
    ContinuousOn (RatChart.ratMap p q) {x | eval x q ≠ 0} :=
  continuousOn_pi.2 fun r =>
    (MvPolynomial.continuous_eval (p r)).continuousOn.div (MvPolynomial.continuous_eval q).continuousOn
      fun _ hx => hx

theorem isOpen_ratPreimage (p : Fin d → MvPolynomial (Fin n) ℂ) (q : MvPolynomial (Fin n) ℂ)
    {S : Set (Fin d → ℂ)} (hS : IsOpen S) :
    IsOpen ({x | eval x q ≠ 0} ∩ RatChart.ratMap p q ⁻¹' S) :=
  (continuousOn_ratMap p q).isOpen_inter_preimage
    (isOpen_ne_fun (MvPolynomial.continuous_eval q) continuous_const) hS

theorem exists_sheet_nhds {J : Ideal (MvPolynomial (Fin n) ℂ)} {p : Fin d → MvPolynomial (Fin n) ℂ}
    {q : MvPolynomial (Fin n) ℂ} (x : Fin n → ℂ) :
    ∃ (s : (Fin d → ℂ) → Fin n → ℂ) (U : Set (Fin d → ℂ)) (W : Set (Fin n → ℂ)),
      IsOpen U ∧ IsOpen W ∧ DifferentiableOn ℂ s U ∧
      (∀ x' ∈ zeroSet J ∩ W, RatChart.ratMap p q x' ∈ U ∧ RatChart.IsRatSheetAt J p q x' s) ∧
      ((∃ s, RatChart.IsRatSheetAt J p q x s) → x ∈ W) := by
  by_cases hx : ∃ s, RatChart.IsRatSheetAt J p q x s
  · obtain ⟨s, U, hU, hxU, hsd, hsx, hsec, V, hV, hVs⟩ := hx
    have hqx : eval x q ≠ 0 := hsx ▸ (hsec _ hxU).2.1
    refine ⟨s, U, interior V ∩ ({x | eval x q ≠ 0} ∩ RatChart.ratMap p q ⁻¹' U), hU,
      isOpen_interior.inter (isOpen_ratPreimage p q hU), hsd, ?_, fun _ =>
        ⟨mem_interior_iff_mem_nhds.2 hV, hqx, hxU⟩⟩
    rintro x' ⟨hx'Z, hx'V, hx'q, hx'U⟩
    have hx's : s (RatChart.ratMap p q x') = x' := (hVs x' ⟨hx'Z, interior_subset hx'V⟩ hx'q hx'U).symm
    exact ⟨hx'U, U, hU, hx'U, hsd, hx's, hsec, interior V, isOpen_interior.mem_nhds hx'V,
      fun x'' hx'' hq'' hR'' => hVs x'' ⟨hx''.1, interior_subset hx''.2⟩ hq'' hR''⟩
  · exact ⟨fun _ => x, ∅, ∅, isOpen_empty, isOpen_empty, differentiableOn_empty,
      by simp, fun h => absurd h hx⟩

theorem exists_sheet_of_det_ne_zero {J : Ideal (MvPolynomial (Fin n) ℂ)}
    {p : Fin d → MvPolynomial (Fin n) ℂ} {q : MvPolynomial (Fin n) ℂ} {A : Matrix (Fin d) (Fin n) ℂ}
    {x : Fin n → ℂ} {s : (Fin d → ℂ) → Fin n → ℂ} (hs : RatChart.IsRatSheetAt J p q x s)
    (hdet : (ReciprocityTheory.AnForm.A.jacC (fun w => A *ᵥ s w) (RatChart.ratMap p q x)).det ≠ 0) :
    ∃ s', IsSheetAt J A x s' := by
  obtain ⟨U, hU, hyU, hsd, hsx, hsec, V, hV, hVs⟩ := hs
  set R := RatChart.ratMap p q with hRdef
  set F : (Fin d → ℂ) → Fin d → ℂ := fun w => A *ᵥ s w with hFdef
  have hFa := SheetOnlyNull.analyticOnNhd_of_differentiableOn hU (SheetOnlyNull.differentiableOn_mulVec A hsd)
  set G : Set (Fin d → ℂ) := U ∩ (fun w => (ReciprocityTheory.AnForm.A.jacC F w).det) ⁻¹' {0}ᶜ with hGdef
  have hG : IsOpen G :=
    (SheetOnlyNull.analyticOnNhd_det_jacC hU (SheetOnlyNull.differentiableOn_mulVec A hsd)).continuousOn
      |>.isOpen_inter_preimage hU isOpen_compl_singleton
  have hinj : ∀ w, (ReciprocityTheory.AnForm.A.jacC F w).det ≠ 0 → Function.Injective (fderiv ℂ F w) :=
    fun w hw => (SheetOnlyNull.injective_iff_det_ne_zero _).2 (by rwa [← ReciprocityTheory.AnForm.A.det_jacC])
  have hequiv : ∀ w ∈ G, ∃ e : (Fin d → ℂ) ≃L[ℂ] (Fin d → ℂ),
      HasStrictFDerivAt F (e : (Fin d → ℂ) →L[ℂ] (Fin d → ℂ)) w := by
    intro w hw
    refine ⟨(LinearEquiv.ofInjectiveEndo _ (hinj w hw.2)).toContinuousLinearEquiv, ?_⟩
    exact (hFa w hw.1).hasStrictFDerivAt.congr_fderiv (ContinuousLinearMap.ext fun v => rfl)
  obtain ⟨e, he⟩ := hequiv _ ⟨hyU, hdet⟩
  set φ := he.toOpenPartialHomeomorph F with hφdef
  have hφ : ∀ w, φ w = F w := fun w => by rw [hφdef, HasStrictFDerivAt.toOpenPartialHomeomorph_coe]
  have hysrc : R x ∈ φ.source := he.mem_toOpenPartialHomeomorph_source
  have hFx : F (R x) = A *ᵥ x := by simp only [hFdef, hsx]
  have hsym : φ.symm (A *ᵥ x) = R x := by rw [← hFx, ← hφ, φ.left_inv hysrc]
  have hqx : eval x q ≠ 0 := hsx ▸ (hsec _ hyU).2.1
  refine ⟨s ∘ φ.symm, φ.target ∩ φ.symm ⁻¹' G, φ.isOpen_inter_preimage_symm hG,
    ⟨by rw [← hFx, ← hφ]; exact φ.map_source hysrc, by rw [Set.mem_preimage, hsym]; exact ⟨hyU, hdet⟩⟩,
    ?_, by simp only [Function.comp_apply, hsym, hsx], fun z hz => ⟨?_, (hsec _ hz.2.1).1⟩, ?_⟩
  · intro z ⟨hzT, hzG⟩
    obtain ⟨e', he'⟩ := hequiv _ hzG
    have hsymd : HasFDerivAt φ.symm _ z :=
      φ.hasFDerivAt_symm hzT (f' := e') (by
        have : (φ : (Fin d → ℂ) → Fin d → ℂ) = F := funext hφ
        rw [this]; exact he'.hasFDerivAt)
    exact ((hsd.differentiableAt (hU.mem_nhds hzG.1)).comp z
      hsymd.differentiableAt).differentiableWithinAt
  · show F (φ.symm z) = z
    rw [← hφ, φ.right_inv hz.1]
  · refine ⟨V ∩ ({x | eval x q ≠ 0} ∩ R ⁻¹' (φ.source ∩ U)), inter_mem hV
      ((isOpen_ratPreimage p q (φ.open_source.inter hU)).mem_nhds ⟨hqx, hysrc, hyU⟩), ?_⟩
    rintro x'' ⟨hx''Z, hx''V, hx''q, hx''src, hx''U⟩ -
    have hx'' : x'' = s (R x'') := hVs x'' ⟨hx''Z, hx''V⟩ hx''q hx''U
    have hA : A *ᵥ x'' = φ (R x'') := by rw [hφ, hFdef]; exact congrArg _ hx''
    rw [Function.comp_apply, hA, φ.left_inv hx''src]
    exact hx''

theorem exists_det_ne_zero (h₁ : IndefiniteRowSideFullHecke.ComplexSets.FiniteMapOpen.Statement)
    (h₂ : IndefiniteRowSideFullHecke.ComplexSets.CriticalImageNull.Statement) {J : Ideal (MvPolynomial (Fin n) ℂ)}
    {p : Fin d → MvPolynomial (Fin n) ℂ} {q : MvPolynomial (Fin n) ℂ} {A : Matrix (Fin d) (Fin n) ℂ}
    (hJ : J.IsPrime) (hA : IsFiniteProjection J A)
    {x : Fin n → ℂ} {s : (Fin d → ℂ) → Fin n → ℂ} (hs : RatChart.IsRatSheetAt J p q x s)
    {W₀ : Set (Fin d → ℂ)} (hW₀ : IsOpen W₀) (hxW₀ : RatChart.ratMap p q x ∈ W₀) :
    ∃ w ∈ W₀, (ReciprocityTheory.AnForm.A.jacC (fun w => A *ᵥ s w) w).det ≠ 0 := by
  obtain ⟨U, hU, hyU, hsd, hsx, hsec, V, hV, hVs⟩ := hs
  set R := RatChart.ratMap p q with hRdef
  set F : (Fin d → ℂ) → Fin d → ℂ := fun w => A *ᵥ s w with hFdef
  by_contra hall
  push Not at hall
  have hcrit : F '' (W₀ ∩ U) ⊆ F '' {w | w ∈ U ∧ ¬ Function.Injective (fderiv ℂ F w)} :=
    Set.image_mono fun w hw => ⟨hw.2, fun hinj => (SheetOnlyNull.injective_iff_det_ne_zero _).1 hinj
      (by rw [← ReciprocityTheory.AnForm.A.det_jacC]; exact hall w hw.1)⟩
  have hnull := measure_mono_null hcrit (h₂ d d U F hU (SheetOnlyNull.differentiableOn_mulVec A hsd))
  have hxZ : x ∈ zeroSet J := hsx ▸ (hsec _ hyU).1
  have hqx : eval x q ≠ 0 := hsx ▸ (hsec _ hyU).2.1
  have hnhds := h₁ n d J (linPoly A) hJ hA.injective hA.finite x hxZ
    (V ∩ ({x | eval x q ≠ 0} ∩ R ⁻¹' (W₀ ∩ U)))
    (inter_mem hV ((isOpen_ratPreimage p q (hW₀.inter hU)).mem_nhds ⟨hqx, hxW₀, hyU⟩))
  have hev : ∀ z : Fin n → ℂ, (fun i => eval z (linPoly A i)) = A *ᵥ z := fun z => by
    ext i
    simp [linPoly, Matrix.mulVec, dotProduct]
  simp only [hev] at hnhds
  have hsub : (fun z => A *ᵥ z) '' (IndefiniteRowSideFullHecke.ComplexSets.zeroLocus J ∩
      (V ∩ ({x | eval x q ≠ 0} ∩ R ⁻¹' (W₀ ∩ U)))) ⊆ F '' (W₀ ∩ U) := by
    rintro _ ⟨z, ⟨hzZ, hzV, hzq, hzW⟩, rfl⟩
    refine ⟨R z, hzW, ?_⟩
    simp only [hFdef]
    rw [← hVs z ⟨hzZ, hzV⟩ hzq hzW.2]
  have hpos := Measure.measure_pos_of_mem_nhds (μ := μH[(Module.finrank ℝ (Fin d → ℂ) : ℝ)])
    (Filter.mem_of_superset hnhds hsub)
  rw [SheetOnlyNull.finrank_real_fin_complex] at hpos
  exact hpos.ne' hnull

end RatSheetNoChartNull

theorem RatSheetNoChartNull.proof : RatSheetNoChartNull.Statement := by
  intro n d J A p q hJ _ hA _
  set B := {x | x ∈ zeroSet J ∧ (∃ s, RatChart.IsRatSheetAt J p q x s) ∧ ¬ ∃ s', IsSheetAt J A x s'}
    with hBdef
  choose σ U W hU hW hσd hWsh hxW using
    fun x : Fin n → ℂ => RatSheetNoChartNull.exists_sheet_nhds (J := J) (p := p) (q := q) x
  obtain ⟨T, hTc, hTU⟩ := TopologicalSpace.isOpen_iUnion_countable W hW
  have hpiece : ∀ i, volume (RatChart.ratMap p q '' (B ∩ W i)) = 0 := by
    intro i
    apply ReciprocityTheory.AnForm.volume_eq_zero_of_locally_in_analytic_zero_set
    rintro _ ⟨x, ⟨hxB, hxWi⟩, rfl⟩
    obtain ⟨hRx, hsh⟩ := hWsh i x ⟨hxB.1, hxWi⟩
    obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp (hU i) _ hRx
    refine ⟨Metric.ball (RatChart.ratMap p q x) r, Metric.isOpen_ball, Metric.mem_ball_self hr,
      (convex_ball _ r).isPreconnected,
      fun w => (ReciprocityTheory.AnForm.A.jacC (fun v => A *ᵥ σ i v) w).det,
      (SheetOnlyNull.analyticOnNhd_det_jacC (hU i)
        (SheetOnlyNull.differentiableOn_mulVec A (hσd i))).mono hball,
      RatSheetNoChartNull.exists_det_ne_zero IndefiniteRowSideFullHecke.ComplexSets.FiniteMapOpen.proof
        IndefiniteRowSideFullHecke.ComplexSets.CriticalImageNull.proof hJ hA hsh Metric.isOpen_ball (Metric.mem_ball_self hr),
      ?_⟩
    rintro _ ⟨⟨x'', ⟨hx''B, hx''W⟩, rfl⟩, -⟩
    by_contra hne
    exact hx''B.2.2 (RatSheetNoChartNull.exists_sheet_of_det_ne_zero (hWsh i x'' ⟨hx''B.1, hx''W⟩).2 hne)
  refine measure_mono_null ?_ ((measure_biUnion_null_iff hTc).2 fun i _ => hpiece i)
  rintro _ ⟨x, hxB, rfl⟩
  have hx : x ∈ ⋃ i ∈ T, W i := hTU ▸ Set.mem_iUnion.2 ⟨x, hxW x hxB.2.1⟩
  obtain ⟨i, hiT, hxi⟩ := Set.mem_iUnion₂.1 hx
  exact Set.mem_biUnion hiT ⟨x, ⟨hxB, hxi⟩, rfl⟩

end

end GroundTheory.Heights₂.Heights
