import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StSliceBoundaryBound
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StSliceFormMass
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PCutOffBoundaryBound
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PMaDensLeibniz
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PSliceIdeal
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PSliceSectionMass
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PFormIntSymm
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PConeChartGram
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PSheetLogNormDens
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.PartsAlg
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Filter Topology Matrix ComplexSets ReciprocityTheory.AnForm ReciprocityTheory.AnForm.A
open GroundTheory.Heights₂.Heights.LowerBoundFree.FubiniLevi CutOffBoundaryBound
open scoped ContDiff

noncomputable section

namespace SliceBoundaryBound

theorem levi_log_dualNorm_comp_nonneg {n D : ℕ} (h : HermNorm n) {τ : (Fin D → ℂ) → Fin n → ℂ}
    {z : Fin D → ℂ} (hτ : AnalyticAt ℂ τ z) (hz : τ z ≠ 0) (ξ : Fin D → ℂ) :
    0 ≤ levi ((fun x => Real.log (h.dualNorm x)) ∘ τ) z ξ := by
  let L : (Fin n → ℂ) →L[ℂ] (Fin (n + 1) → ℂ) :=
    LinearMap.toContinuousLinearMap (Matrix.mulVecLin (FubiniStudyLogRegularization.regMat h 0 1))
  have hL : ∀ x, L x = FubiniStudyLogRegularization.regMat h 0 1 *ᵥ x := fun x => rfl
  have hσ : AnalyticAt ℂ (L ∘ τ) z := (L.analyticAt _).comp hτ
  have hS : sqSum ((L ∘ τ) z) ≠ 0 := by
    rw [Function.comp_apply, hL]
    exact SheetLogNormDensity.sqSum_ne_zero (FubiniStudyLogRegularization.regMat_mulVec_ne_zero h 0 one_pos hz)
  have hfun : (fun x => Real.log (h.dualNorm x)) ∘ τ = phi ∘ (L ∘ τ) := by
    funext y
    simp only [Function.comp_apply, hL]
    rw [FubiniStudyLogRegularization.log_dualNorm_eq]
    exact SheetLogNormDensity.log_sqrt_eq_phi _
  rw [hfun, levi_comp ξ hσ (contDiffAt_phi hS)]
  exact GroundTheory.Heights₂.Heights.Inter.TorusInvariantLevi.leviForm_phi_nonneg hS _

theorem exists_psh_nhd {n D : ℕ} (h : HermNorm n) {s : (Fin D → ℂ) → Fin n → ℂ} {y : Fin D → ℂ}
    (hs : AnalyticAt ℂ s y) (hy : s y ≠ 0) :
    ∃ U : Set (Fin D → ℂ), IsOpen U ∧ y ∈ U ∧
      ContDiffOn ℝ 2 ((fun x => Real.log (h.dualNorm x)) ∘ s) U ∧
      ∀ z ∈ U, ∀ ξ, 0 ≤ levi ((fun x => Real.log (h.dualNorm x)) ∘ s) z ξ := by
  have hev : ∀ᶠ z in 𝓝 y, AnalyticAt ℂ s z ∧ s z ≠ 0 :=
    hs.eventually_analyticAt.and (hs.continuousAt.eventually_ne hy)
  obtain ⟨U, hU, hUo, hyU⟩ := eventually_nhds_iff.mp hev
  refine ⟨U, hUo, hyU, fun z hz => ?_, fun z hz ξ =>
    levi_log_dualNorm_comp_nonneg h (hU z hz).1 (hU z hz).2 ξ⟩
  have hc : ContDiffAt ℝ 2 (fun x => Real.log (h.dualNorm x)) (s z) :=
    ((contDiffOn_log_dualNorm h).contDiffAt (isOpen_compl_singleton.mem_nhds (hU z hz).2)).of_le
      (WithTop.coe_le_coe.mpr le_top)
  exact (hc.comp z (hU z hz).1.restrictScalars.contDiffAt).contDiffWithinAt

theorem abs_le_of_sq_le {v a b : ℝ} (ha : 0 ≤ a) (h : v ^ 2 ≤ a * b) : |v| ≤ 1 * √a * √b := by
  rw [one_mul, ← Real.sqrt_mul ha]
  exact Real.abs_le_sqrt h

theorem vecCons_log_eq {n e : ℕ} (h : HermNorm n) (f : (Fin n → ℂ) → ℝ) :
    (vecCons f fun _ x => Real.log (h.dualNorm x) : Fin (e + 1) → (Fin n → ℂ) → ℝ) =
      fun k x => (vecCons 0 fun _ => 1 : Fin (e + 1) → ℝ) k * Real.log (h.dualNorm x) +
        (vecCons f fun _ _ => 0 : Fin (e + 1) → (Fin n → ℂ) → ℝ) k x := by
  funext k x
  refine Fin.cases ?_ (fun i => ?_) k <;> simp

end SliceBoundaryBound

open SliceBoundaryBound in

theorem SliceBoundaryBound.proof (hM : ChartMassCompact.Statement) (hSM : SliceFormMass.Statement) :
    SliceBoundaryBound.Statement := by
  intro n e h W g ℓ A F G hW hg hℓ hA hF0 hG0 hFs hGs
  obtain ⟨hIp, hdim, -⟩ := SliceIdeal.proof n (e + 1) W g ℓ hW hg hℓ
  have hZ0 : ∀ x ∈ zeroSet (W ⊔ Ideal.span {linForm ℓ - 1}), x ≠ 0 :=
    fun x hx => ne_zero_of_mem_zeroSet_slice hx
  have hU0 : IsOpen {x : Fin n → ℂ | x ≠ 0} := isOpen_ne
  have hsm : ∀ f : (Fin n → ℂ) → ℝ, ContDiffOn ℝ ∞ f {x | x ≠ 0} →
      SmoothNear (zeroSet (W ⊔ Ideal.span {linForm ℓ - 1})) f :=
    fun f hf => ⟨_, hU0, fun x hx => hZ0 x hx, hf⟩
  have hLs : ContDiffOn ℝ ∞ (fun x : Fin n → ℂ => Real.log (h.dualNorm x)) {x | x ≠ 0} :=
    (contDiffOn_log_dualNorm h).mono fun x hx => hx
  have hω : ∀ i : Fin e, SmoothNear (zeroSet (W ⊔ Ideal.span {linForm ℓ - 1}))
      ((fun _ x => Real.log (h.dualNorm x)) i : (Fin n → ℂ) → ℝ) := fun _ => hsm _ hLs
  have hcons : ∀ (f : (Fin n → ℂ) → ℝ) (ψ : Fin e → (Fin n → ℂ) → ℝ),
      SmoothNear (zeroSet (W ⊔ Ideal.span {linForm ℓ - 1})) f →
      (∀ i, SmoothNear (zeroSet (W ⊔ Ideal.span {linForm ℓ - 1})) (ψ i)) →
      ∀ i, SmoothNear (zeroSet (W ⊔ Ideal.span {linForm ℓ - 1})) (vecCons f ψ i) := by
    intro f ψ hf hψ i
    refine Fin.cases ?_ (fun i => ?_) i
    · simpa using hf
    · simpa using hψ i
  have hoff : ∀ f : (Fin n → ℂ) → ℝ, ContinuousOn f {x | x ≠ 0} →
      ContinuousOn f (zeroSet (W ⊔ Ideal.span {linForm ℓ - 1})) :=
    fun f hf => hf.mono fun x hx => hZ0 x hx
  have hFc : ContinuousOn F {x | x ≠ 0} := hFs.continuousOn
  have hGc : ContinuousOn G {x | x ≠ 0} := hGs.continuousOn

  have hslice : ∀ w f : (Fin n → ℂ) → ℝ, (∀ (t : ℂ) (x : Fin n → ℂ), t ≠ 0 → w (t • x) = w x) →
      ContinuousOn w {x | x ≠ 0} → (∀ (t : ℂ) (x : Fin n → ℂ), t ≠ 0 → f (t • x) = f x) →
      ContDiffOn ℝ ∞ f {x | x ≠ 0} →
      Integrable (chartDens (W ⊔ Ideal.span {linForm ℓ - 1}) A w
        (vecCons f fun _ x => Real.log (h.dualNorm x))) := by
    intro w f hw0 hwc hf0 hfs
    have hI := hSM n e h W g ℓ A w (vecCons 0 fun _ => 1) (vecCons f fun _ _ => 0) hW hg hℓ hA hw0 hwc
      (fun k => Fin.cases (fun t x ht => by simpa using hf0 t x ht) (fun i t x _ => by simp) k)
      (fun k => Fin.cases (by simpa using hfs) (fun i => by simpa using contDiffOn_const) k)
    rw [← vecCons_log_eq] at hI
    exact hI.mono' (measurable_chartDens hIp hdim hA (hoff w hwc) (hcons _ _ (hsm f hfs) hω)).aestronglyMeasurable
      (Eventually.of_forall fun y => by simpa [Real.norm_eq_abs] using abs_chartDens_le _ A _ _ y)
  have hG2 : ∀ (t : ℂ) (x : Fin n → ℂ), t ≠ 0 → (fun x => G x ^ 2) (t • x) = (fun x => G x ^ 2) x :=
    fun t x ht => by simp only [hG0 t x ht]
  have hf₁ := hslice (fun x => G x ^ 2) (fun x => F x ^ 2 / 2) hG2 (hGc.pow 2)
    (fun t x ht => by simp only [hF0 t x ht]) ((hFs.pow 2).div_const 2)
  have hf₂ := hslice (fun x => G x ^ 2 * F x) F (fun t x ht => by simp only [hG0 t x ht, hF0 t x ht])
    ((hGc.pow 2).mul hFc) hF0 hFs
  set Φ := ∫ y, (chartDens (W ⊔ Ideal.span {linForm ℓ - 1}) A (fun x => G x ^ 2)
      (vecCons (fun x => F x ^ 2 / 2) fun _ x => Real.log (h.dualNorm x)) y -
    chartDens (W ⊔ Ideal.span {linForm ℓ - 1}) A (fun x => G x ^ 2 * F x)
      (vecCons F fun _ x => Real.log (h.dualNorm x)) y) with hΦ

  obtain ⟨M₀, hM₀⟩ := bounded_of_degree_zero (fun x => G x * F x)
    (fun t x ht => by simp only [hG0 t x ht, hF0 t x ht]) (hGc.mul hFc)
  have hM₀0 : 0 ≤ M₀ := (abs_nonneg _).trans (hM₀ 0)
  refine ⟨max M₀ (2 * 1 * √(max Φ 1)), le_max_of_le_left hM₀0, fun χ hχ hχcs => ?_⟩
  have hχc : Continuous χ := hχ.continuous
  have hχn := hsm χ hχ.contDiffOn
  have hχFn := hsm (fun x => χ x * F x) (hχ.contDiffOn.mul hFs)
  have hχ2n := hsm (fun x => χ x ^ 2 / 2) ((hχ.pow 2).div_const 2).contDiffOn
  have hFn := hsm F hFs
  have hχ2cs : HasCompactSupport (fun x => χ x ^ 2 / 2) := hχcs.mono fun x hx h0 => hx (by simp [h0])
  have hD₁ := integrable_chartDens hM hIp hdim hA (hoff G hGc) (hcons _ _ hχFn hω)
    (Or.inr ⟨0, by rw [Matrix.cons_val_zero]; exact (hχcs.mul_right : HasCompactSupport (χ * F))⟩)
  have hD₂ := integrable_chartDens hM hIp hdim hA (f := fun x => χ x * G x)
    (hχc.continuousOn.mul (hoff G hGc)) (hcons _ _ hFn hω)
    (Or.inl (hχcs.mul_right : HasCompactSupport (χ * G)))
  have ha := hM n (e + 1) _ A (fun _ => 1) _ hIp hdim hA continuousOn_const (hcons _ _ hχn hω)
    (Or.inr ⟨0, by rw [Matrix.cons_val_zero]; exact hχcs⟩)
  have he₁ := integrable_chartDens hM hIp hdim hA (f := fun _ => 1) continuousOn_const (hcons _ _ hχ2n hω)
    (Or.inr ⟨0, by rw [Matrix.cons_val_zero]; exact hχ2cs⟩)
  have he₂ := integrable_chartDens hM hIp hdim hA (f := χ) hχc.continuousOn (hcons _ _ hχn hω)
    (Or.inl hχcs)
  have hle2 : (2 : WithTop ℕ∞) ≤ ∞ := WithTop.coe_le_coe.mpr le_top

  have key : ∀ t > 0, ∀ y,
      |chartDens (W ⊔ Ideal.span {linForm ℓ - 1}) A G
          (vecCons (fun x => χ x * F x) fun _ x => Real.log (h.dualNorm x)) y -
        chartDens (W ⊔ Ideal.span {linForm ℓ - 1}) A (fun x => χ x * G x)
          (vecCons F fun _ x => Real.log (h.dualNorm x)) y| ≤
      M₀ * chartAbsDens (W ⊔ Ideal.span {linForm ℓ - 1}) A (fun _ => 1)
          (vecCons χ fun _ x => Real.log (h.dualNorm x)) y +
      1 * t * (chartDens (W ⊔ Ideal.span {linForm ℓ - 1}) A (fun _ => 1)
          (vecCons (fun x => χ x ^ 2 / 2) fun _ x => Real.log (h.dualNorm x)) y -
        chartDens (W ⊔ Ideal.span {linForm ℓ - 1}) A χ (vecCons χ fun _ x => Real.log (h.dualNorm x)) y) +
      1 / t * (chartDens (W ⊔ Ideal.span {linForm ℓ - 1}) A (fun x => G x ^ 2)
          (vecCons (fun x => F x ^ 2 / 2) fun _ x => Real.log (h.dualNorm x)) y -
        chartDens (W ⊔ Ideal.span {linForm ℓ - 1}) A (fun x => G x ^ 2 * F x)
          (vecCons F fun _ x => Real.log (h.dualNorm x)) y) := by
    intro t ht y
    have hfin := (FibreBound.proof n (e + 1) _ A hIp hdim hA y).2.1
    unfold chartDens chartAbsDens
    refine abs_sheetSum_sub_le hfin _ _ _ _ _ _ _ _ _ _ fun x hx s hs => ?_
    obtain ⟨hxZ, hAx⟩ := hx
    have hsx : s y = x := by
      obtain ⟨_, _, _, _, h, -⟩ := hs
      rw [← hAx]
      exact h
    have han : AnalyticAt ℂ s y := by
      rw [← hAx]
      exact analyticAt_of_isSheetAt hs
    have hsc : ContDiffAt ℝ 2 s y := han.restrictScalars.contDiffAt
    have hy0 : s y ≠ 0 := hsx ▸ hZ0 x hxZ
    have c2 : ∀ f : (Fin n → ℂ) → ℝ, ContDiffOn ℝ ∞ f {x | x ≠ 0} → ContDiffAt ℝ 2 (f ∘ s) y :=
      fun f hf => ((hf.contDiffAt (hU0.mem_nhds hy0)).of_le hle2).comp y hsc
    have hχs := c2 χ hχ.contDiffOn
    have hFs' := c2 F hFs
    obtain ⟨U, hUo, hyU, hC2, hlev⟩ := exists_psh_nhd h han hy0
    simp only [vecCons_comp]
    have e₁ : maDens (Fin.cons ((fun x => χ x * F x) ∘ s) fun _ => (fun x => Real.log (h.dualNorm x)) ∘ s) y =
        (χ ∘ s) y * maDens (Fin.cons (F ∘ s) fun _ => (fun x => Real.log (h.dualNorm x)) ∘ s) y +
          (F ∘ s) y * maDens (Fin.cons (χ ∘ s) fun _ => (fun x => Real.log (h.dualNorm x)) ∘ s) y +
            gradDens (fun _ => (fun x => Real.log (h.dualNorm x)) ∘ s) (χ ∘ s) (F ∘ s) y +
            gradDens (fun _ => (fun x => Real.log (h.dualNorm x)) ∘ s) (F ∘ s) (χ ∘ s) y :=
      (MaDensLeibniz.proof e (fun _ => (fun x => Real.log (h.dualNorm x)) ∘ s) (χ ∘ s) (F ∘ s) y hχs hFs').1
    have e₂ : maDens (Fin.cons ((fun x => χ x ^ 2 / 2) ∘ s) fun _ => (fun x => Real.log (h.dualNorm x)) ∘ s) y =
        (χ ∘ s) y * maDens (Fin.cons (χ ∘ s) fun _ => (fun x => Real.log (h.dualNorm x)) ∘ s) y +
          gradDens (fun _ => (fun x => Real.log (h.dualNorm x)) ∘ s) (χ ∘ s) (χ ∘ s) y :=
      (MaDensLeibniz.proof e (fun _ => (fun x => Real.log (h.dualNorm x)) ∘ s) (χ ∘ s) (χ ∘ s) y hχs hχs).2
    have e₃ : maDens (Fin.cons ((fun x => F x ^ 2 / 2) ∘ s) fun _ => (fun x => Real.log (h.dualNorm x)) ∘ s) y =
        (F ∘ s) y * maDens (Fin.cons (F ∘ s) fun _ => (fun x => Real.log (h.dualNorm x)) ∘ s) y +
          gradDens (fun _ => (fun x => Real.log (h.dualNorm x)) ∘ s) (F ∘ s) (F ∘ s) y :=
      (MaDensLeibniz.proof e (fun _ => (fun x => Real.log (h.dualNorm x)) ∘ s) (F ∘ s) (F ∘ s) y hFs' hFs').2
    have hEχ := gradDensNonneg_thm e (fun _ => (fun x => Real.log (h.dualNorm x)) ∘ s) (χ ∘ s) U hUo
      (fun _ => hC2) (fun _ => hlev) y hyU
    have hEF := gradDensNonneg_thm e (fun _ => (fun x => Real.log (h.dualNorm x)) ∘ s) (F ∘ s) U hUo
      (fun _ => hC2) (fun _ => hlev) y hyU
    have h₁ := abs_le_of_sq_le hEχ (gradDensCauchySchwarz_thm e
      (fun _ => (fun x => Real.log (h.dualNorm x)) ∘ s) (χ ∘ s) (F ∘ s) U hUo (fun _ => hC2) (fun _ => hlev) y hyU)
    have h₂ := abs_le_of_sq_le hEF (gradDensCauchySchwarz_thm e
      (fun _ => (fun x => Real.log (h.dualNorm x)) ∘ s) (F ∘ s) (χ ∘ s) U hUo (fun _ => hC2) (fun _ => hlev) y hyU)
    rw [e₁, e₂, e₃]
    simp only [Function.comp_apply, hsx] at hEχ hEF h₁ h₂ ⊢
    rw [show ∀ m E : ℝ, 1 * (χ x * m + E) - χ x * m = 1 * E from fun m E => by ring,
      show ∀ m E : ℝ, G x ^ 2 * (F x * m + E) - G x ^ 2 * F x * m = G x ^ 2 * E from fun m E => by ring]
    exact term_bound ht zero_le_one (hM₀ x) hEχ hEF h₁ h₂

  refine final_bound zero_le_one (integral_nonneg fun y => chartAbsDens_nonneg _ A _ _ y) fun t ht => ?_
  set D₁ := chartDens (W ⊔ Ideal.span {linForm ℓ - 1}) A G
    (vecCons (fun x => χ x * F x) fun _ x => Real.log (h.dualNorm x)) with hD₁def
  set D₂ := chartDens (W ⊔ Ideal.span {linForm ℓ - 1}) A (fun x => χ x * G x)
    (vecCons F fun _ x => Real.log (h.dualNorm x)) with hD₂def
  set a := chartAbsDens (W ⊔ Ideal.span {linForm ℓ - 1}) A (fun _ => 1)
    (vecCons χ fun _ x => Real.log (h.dualNorm x)) with hadef
  set e₁ := chartDens (W ⊔ Ideal.span {linForm ℓ - 1}) A (fun _ => 1)
    (vecCons (fun x => χ x ^ 2 / 2) fun _ x => Real.log (h.dualNorm x)) with he₁def
  set e₂ := chartDens (W ⊔ Ideal.span {linForm ℓ - 1}) A χ
    (vecCons χ fun _ x => Real.log (h.dualNorm x)) with he₂def
  set f₁ := chartDens (W ⊔ Ideal.span {linForm ℓ - 1}) A (fun x => G x ^ 2)
    (vecCons (fun x => F x ^ 2 / 2) fun _ x => Real.log (h.dualNorm x)) with hf₁def
  set f₂ := chartDens (W ⊔ Ideal.span {linForm ℓ - 1}) A (fun x => G x ^ 2 * F x)
    (vecCons F fun _ x => Real.log (h.dualNorm x)) with hf₂def
  have h1 : chartInt (W ⊔ Ideal.span {linForm ℓ - 1}) A G
        (vecCons (fun x => χ x * F x) fun _ x => Real.log (h.dualNorm x)) -
      chartInt (W ⊔ Ideal.span {linForm ℓ - 1}) A (fun x => χ x * G x)
        (vecCons F fun _ x => Real.log (h.dualNorm x)) = ∫ y, (D₁ y - D₂ y) :=
    (integral_sub hD₁ hD₂).symm
  have h2 : chartInt (W ⊔ Ideal.span {linForm ℓ - 1}) A (fun _ => 1)
        (vecCons (fun x => χ x ^ 2 / 2) fun _ x => Real.log (h.dualNorm x)) -
      chartInt (W ⊔ Ideal.span {linForm ℓ - 1}) A χ (vecCons χ fun _ x => Real.log (h.dualNorm x)) =
      ∫ y, (e₁ y - e₂ y) := (integral_sub he₁ he₂).symm
  have h3 : ∫ y, (M₀ * a y + 1 * t * (e₁ y - e₂ y) + 1 / t * (f₁ y - f₂ y)) =
      M₀ * (∫ y, a y) + 1 * t * (∫ y, (e₁ y - e₂ y)) + 1 / t * Φ := by
    rw [integral_add, integral_add, integral_const_mul, integral_const_mul, integral_const_mul]
    all_goals first
      | exact ha.const_mul _
      | exact (he₁.sub he₂).const_mul _
      | exact (hf₁.sub hf₂).const_mul _
      | exact (ha.const_mul _).add ((he₁.sub he₂).const_mul _)
  rw [h1, h2, ← h3]
  refine le_trans ?_ (integral_mono (hD₁.sub hD₂).abs (((ha.const_mul _).add ((he₁.sub he₂).const_mul _)).add
    ((hf₁.sub hf₂).const_mul _)) fun y => key t ht y)
  exact (by simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm fun y => D₁ y - D₂ y :
    |∫ y, (D₁ y - D₂ y)| ≤ ∫ y, |D₁ y - D₂ y|)

end

end GroundTheory.Heights₂.Heights
