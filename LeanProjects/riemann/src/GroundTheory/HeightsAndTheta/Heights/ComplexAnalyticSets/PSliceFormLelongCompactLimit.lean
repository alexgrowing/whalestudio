import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StChartMassCompact
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PChartMassCompact
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PLelongRegularise
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PCutOffDominated
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.SliceCut
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StatementsGreenReg
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PConeLogBound
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Filter Topology Matrix ComplexSets
open scoped ContDiff Manifold

noncomputable section

namespace SliceFormLelongCompact

variable {n d : ℕ}

theorem ne_zero_of_mem_zeroSet {I : Ideal (MvPolynomial (Fin n) ℂ)} {ℓ : Fin n → ℂ}
    (hℓ : linForm ℓ - 1 ∈ I) {x : Fin n → ℂ} (hx : x ∈ zeroSet I) : x ≠ 0 := by
  rintro rfl
  have := hx _ hℓ
  simp [linForm] at this

theorem zeroSet_anti {I I' : Ideal (MvPolynomial (Fin n) ℂ)} (hle : I ≤ I') : zeroSet I' ⊆ zeroSet I :=
  fun _ hx p hp => hx p (hle hp)

theorem varInt_congr_weight {J : Ideal (MvPolynomial (Fin n) ℂ)} {f g : (Fin n → ℂ) → ℝ}
    (hfg : ∀ x ∈ zeroSet J, f x = g x) (φ : Fin d → (Fin n → ℂ) → ℝ) : varInt J d f φ = varInt J d g φ := by
  unfold varInt chartInt
  split_ifs with hA
  · rw [CutOffDominated.chartDens_congr_zeroSet hfg]
  · rfl

theorem exists_contDiff_eqOn {Z : Set (Fin n → ℂ)} {f : (Fin n → ℂ) → ℝ} (hZ : IsClosed Z)
    (hf : SmoothNear Z f) (hfc : HasCompactSupport f) :
    ∃ g : (Fin n → ℂ) → ℝ, ContDiff ℝ ∞ g ∧ HasCompactSupport g ∧ ∀ x ∈ Z, g x = f x := by
  obtain ⟨U, hU, hZU, hfU⟩ := hf
  have hK : IsCompact (Z ∩ tsupport f) := hfc.isCompact.inter_left hZ
  obtain ⟨V, hVo, hKV, hVU, -⟩ := exists_open_between_and_isCompact_closure hK hU
    (Set.inter_subset_left.trans hZU)
  obtain ⟨θ, hθ, -, h0, h1⟩ := exists_contMDiff_zero_iff_one_iff_of_isClosed
    (I := 𝓘(ℝ, Fin n → ℂ)) (n := ⊤) hVo.isClosed_compl hK.isClosed
    (Set.disjoint_compl_left_iff_subset.2 hKV)
  have hθc : ContDiff ℝ ∞ θ := contMDiff_iff_contDiff.1 hθ
  have hsupp : tsupport θ ⊆ U := by
    refine (closure_mono fun y hy => ?_).trans hVU
    by_contra hyV
    exact hy ((h0 y).1 hyV)
  refine ⟨fun x => θ x * f x, contDiff_iff_contDiffAt.2 fun x => ?_, hfc.mul_left, fun x hx => ?_⟩
  · by_cases hxU : x ∈ U
    · exact hθc.contDiffAt.mul (hfU.contDiffAt (hU.mem_nhds hxU))
    · have hθ0 : θ =ᶠ[𝓝 x] 0 := notMem_tsupport_iff_eventuallyEq.1 fun h => hxU (hsupp h)
      refine (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq ?_
      filter_upwards [hθ0] with y hy
      simp [hy]
  · show θ x * f x = f x
    by_cases hxf : x ∈ tsupport f
    · rw [(h1 x).1 ⟨hx, hxf⟩, one_mul]
    · rw [image_eq_zero_of_notMem_tsupport hxf, mul_zero]

theorem chartAbsDens_indicator_eq {J : Ideal (MvPolynomial (Fin n) ℂ)} {A : Matrix (Fin d) (Fin n) ℂ}
    (w : (Fin n → ℂ) → ℝ) (ψ : Fin d → (Fin n → ℂ) → ℝ) {B : Set (Fin n → ℂ)} (i : Fin d)
    (hB : tsupport (ψ i) ⊆ B) : chartAbsDens J A (B.indicator w) ψ = chartAbsDens J A w ψ := by
  funext y
  unfold chartAbsDens sheetSum
  refine finsum_congr fun x => finsum_congr fun hx => ?_
  split_ifs with hs
  · by_cases hxB : x ∈ B
    · dsimp only
      rw [Set.indicator_of_mem hxB]
    · have hM := ChartMassCompact.maDens_eq_zero hs.choose_spec ψ i fun h => hxB (hB h)
      rw [hx.2] at hM
      simp [hM]
  · rfl

theorem integrable_chartDens {J : Ideal (MvPolynomial (Fin n) ℂ)} {A : Matrix (Fin d) (Fin n) ℂ}
    (hA : IsFiniteProjection J A) {w : (Fin n → ℂ) → ℝ} {ψ : Fin d → (Fin n → ℂ) → ℝ}
    (hm : Measurable (chartDens J A w ψ)) (hi : Integrable (chartAbsDens J A w ψ)) :
    Integrable (chartDens J A w ψ) := by
  refine hi.mono' hm.aestronglyMeasurable (Eventually.of_forall fun y => ?_)
  have hfin := IndefiniteRowSideFullHecke.ComplexSets.fibre_finite hA y
  rw [Real.norm_eq_abs]
  unfold chartDens chartAbsDens sheetSum
  rw [finsum_mem_eq_finite_toFinset_sum _ hfin, finsum_mem_eq_finite_toFinset_sum _ hfin]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun x _ => ?_)
  split_ifs <;> simp

theorem measurable_fsLogReg (h : HermNorm n) (u : Fin n → ℂ) (ε : ℝ) : Measurable (fsLogReg h u ε) := by
  have hN : Measurable h.dualNorm := (SliceCut.continuous_dualNorm h).measurable
  have hL : Measurable fun y : Fin n → ℂ => ‖∑ j, u j * y j‖ := (by fun_prop : Continuous _).measurable
  unfold fsLogReg
  fun_prop

theorem abs_fsLogReg_le (h : HermNorm n) (u x : Fin n → ℂ) {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1)
    (hu : linEval u x ≠ 0) (hx : 0 < h.dualNorm x) :
    |fsLogReg h u ε x| ≤ 2 * |Real.log ‖linEval u x‖| + (2 * |Real.log (h.dualNorm x)| + 1) := by
  have ht : 0 < ‖linEval u x‖ := norm_pos_iff.2 hu
  have he : fsLogReg h u ε x = Real.log ((‖linEval u x‖ / h.dualNorm x) ^ 2 + ε) / 2 := by
    unfold fsLogReg linEval
    congr 2
    field_simp
  rw [he]
  refine (LelongRegularise.abs_half_log_le (div_pos ht hx) hε hε1).trans ?_
  rw [Real.log_mul two_ne_zero (div_pos ht hx).ne', Real.log_div ht.ne' hx.ne']
  have h2 : Real.log 2 ≤ 1 := by
    have := Real.log_le_sub_one_of_pos (two_pos : (0 : ℝ) < 2)
    linarith
  have h2' : 0 ≤ Real.log 2 := Real.log_nonneg one_le_two
  have a1 := abs_sub (Real.log ‖linEval u x‖) (Real.log (h.dualNorm x))
  have a2 := abs_add_le (Real.log 2) (Real.log ‖linEval u x‖ - Real.log (h.dualNorm x))
  rw [abs_of_nonneg h2'] at a2
  linarith

theorem tendsto_fsLogReg_sub (h : HermNorm n) (u x : Fin n → ℂ) (hu : linEval u x ≠ 0)
    (hx : 0 < h.dualNorm x) :
    Tendsto (fun ε => fsLogReg h u ε x) (𝓝[>] 0)
      (𝓝 (Real.log ‖linEval u x‖ - Real.log (h.dualNorm x))) := by
  have := (fsLogReg_tendsto h u x hx hu).mono_left (nhdsWithin_le_nhds (s := Set.Ioi 0))
  have e : Real.log (‖∑ j, u j * x j‖ / h.dualNorm x) =
      Real.log ‖linEval u x‖ - Real.log (h.dualNorm x) :=
    Real.log_div (norm_pos_iff.2 hu).ne' hx.ne'
  rwa [fsLog, e] at this

theorem norm_chartDens_fsLogReg_le (h : HermNorm n) {J : Ideal (MvPolynomial (Fin n) ℂ)}
    {A : Matrix (Fin (d + 1)) (Fin n) ℂ} (hA : IsFiniteProjection J A) {u : Fin n → ℂ}
    {f : (Fin n → ℂ) → ℝ} (φ : Fin d → (Fin n → ℂ) → ℝ) {R : ℝ}
    (hR : tsupport f ⊆ Metric.closedBall 0 R) (h0 : ∀ x ∈ zeroSet J, x ≠ 0) {ε : ℝ} (hε : 0 < ε)
    (hε1 : ε ≤ 1) {y : Fin (d + 1) → ℂ} (hy : ∀ x ∈ fibre J A y, linEval u x ≠ 0) :
    ‖chartDens J A (fsLogReg h u ε) (vecCons f φ) y‖ ≤
      2 * chartAbsDens J A ((Metric.closedBall 0 R).indicator fun x => Real.log ‖linEval u x‖)
          (vecCons f φ) y +
        chartAbsDens J A (fun x => 2 * |Real.log (h.dualNorm x)| + 1) (vecCons f φ) y := by
  have hfin := IndefiniteRowSideFullHecke.ComplexSets.fibre_finite hA y
  unfold chartDens chartAbsDens sheetSum
  rw [finsum_mem_eq_finite_toFinset_sum _ hfin, finsum_mem_eq_finite_toFinset_sum _ hfin,
    finsum_mem_eq_finite_toFinset_sum _ hfin, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun x hx => ?_)
  rw [Set.Finite.mem_toFinset] at hx
  by_cases hs : ∃ s, IsSheetAt J A x s
  · simp only [dif_pos hs]
    by_cases hxB : x ∈ Metric.closedBall 0 R
    · have hb := abs_fsLogReg_le h u x hε hε1 (hy x hx) (h.dualNorm_pos (h0 x hx.1))
      have hpos : (0 : ℝ) ≤ 2 * |Real.log (h.dualNorm x)| + 1 := by positivity
      rw [Set.indicator_of_mem hxB, Real.norm_eq_abs]
      simp only [abs_mul]
      rw [abs_of_nonneg hpos]
      exact (mul_le_mul_of_nonneg_right hb (abs_nonneg _)).trans (le_of_eq (by ring))
    · have hM := ChartMassCompact.maDens_eq_zero hs.choose_spec (vecCons f φ) 0
        (by simpa using fun h' => hxB (hR h'))
      rw [hx.2] at hM
      rw [hM]
      simp
  · simp only [dif_neg hs]
    simp

theorem tendsto_chartDens_fsLogReg (h : HermNorm n) {J : Ideal (MvPolynomial (Fin n) ℂ)}
    {A : Matrix (Fin d) (Fin n) ℂ} (hA : IsFiniteProjection J A) (u : Fin n → ℂ)
    (ψ : Fin d → (Fin n → ℂ) → ℝ) (h0 : ∀ x ∈ zeroSet J, x ≠ 0) {y : Fin d → ℂ}
    (hy : ∀ x ∈ fibre J A y, linEval u x ≠ 0) :
    Tendsto (fun ε => chartDens J A (fsLogReg h u ε) ψ y) (𝓝[>] 0)
      (𝓝 (chartDens J A (fun x => Real.log ‖linEval u x‖) ψ y -
        chartDens J A (fun x => Real.log (h.dualNorm x)) ψ y)) := by
  have hfin := IndefiniteRowSideFullHecke.ComplexSets.fibre_finite hA y
  unfold chartDens sheetSum
  simp only [finsum_mem_eq_finite_toFinset_sum _ hfin, ← Finset.sum_sub_distrib]
  refine tendsto_finsetSum _ fun x hx => ?_
  rw [Set.Finite.mem_toFinset] at hx
  by_cases hs : ∃ s, IsSheetAt J A x s
  · simp only [dif_pos hs, ← sub_mul]
    exact (tendsto_fsLogReg_sub h u x (hy x hx) (h.dualNorm_pos (h0 x hx.1))).mul_const _
  · simp only [dif_neg hs, sub_zero]
    exact tendsto_const_nhds

theorem tendsto_varInt_fsLogReg (hLI : LogIntegrable.Statement) (hCM : ChartMassCompact.Statement)
    (h : HermNorm n) (J : Ideal (MvPolynomial (Fin n) ℂ)) (u : Fin n → ℂ) (f : (Fin n → ℂ) → ℝ)
    (φ : Fin d → (Fin n → ℂ) → ℝ) (hJ : J.IsPrime)
    (hdim : ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = (d + 1 : ℕ)) (hu : linForm u ∉ J)
    (h0 : ∀ x ∈ zeroSet J, x ≠ 0) (hf : SmoothNear (zeroSet J) f) (hfc : HasCompactSupport f)
    (hφ : ∀ i, SmoothNear (zeroSet J) (φ i)) :
    Tendsto (fun ε => varInt J (d + 1) (fsLogReg h u ε) (vecCons f φ)) (𝓝[>] 0)
      (𝓝 (varInt J (d + 1) (fun x => Real.log ‖linEval u x‖) (vecCons f φ) -
        varInt J (d + 1) (fun x => Real.log (h.dualNorm x)) (vecCons f φ))) := by
  unfold varInt
  split_ifs with hA
  swap
  · simp only [sub_zero]
    exact (tendsto_const_nhds : Tendsto (fun _ : ℝ => (0 : ℝ)) (𝓝[>] 0) (𝓝 0))
  have hAf := hA.choose_spec
  unfold chartInt
  obtain ⟨R, hR⟩ := hfc.isCompact.isBounded.subset_closedBall (0 : Fin n → ℂ)
  have hψ : ∀ i, SmoothNear (zeroSet J) (vecCons f φ i) := fun i =>
    Fin.cases (by simpa using hf) (fun i => by simpa using hφ i) i
  have hcs : HasCompactSupport (vecCons f φ 0) := by simpa using hfc
  have hcN : ContinuousOn (fun x => Real.log (h.dualNorm x)) (zeroSet J) :=
    (contDiffOn_log_dualNorm h).continuousOn.mono fun x hx => h0 x hx
  have hmN : Measurable fun x : Fin n → ℂ => Real.log (h.dualNorm x) :=
    Real.measurable_log.comp (SliceCut.continuous_dualNorm h).measurable
  have hmU : Measurable fun x : Fin n → ℂ => Real.log ‖linEval u x‖ :=
    Real.measurable_log.comp (Continuous.measurable (by unfold linEval; fun_prop))
  have hmeas : ∀ w, Measurable w → Measurable (chartDens J hA.choose w (vecCons f φ)) := fun w hw =>
    (SheetSumMeasurable.proof n (d + 1) J hA.choose w _ hJ hdim hAf hw hψ).1
  have hI1 := hLI n (d + 1) J hA.choose u (vecCons f φ) R hJ hdim hAf hu hψ
  have hI2 := hCM n (d + 1) J hA.choose (fun x => 2 * |Real.log (h.dualNorm x)| + 1) (vecCons f φ) hJ hdim
    hAf ((hcN.abs.const_smul (2 : ℝ)).add continuousOn_const) hψ (Or.inr ⟨0, hcs⟩)
  have hIN := hCM n (d + 1) J hA.choose _ (vecCons f φ) hJ hdim hAf hcN hψ (Or.inr ⟨0, hcs⟩)
  have hIU : Integrable (chartAbsDens J hA.choose (fun x => Real.log ‖linEval u x‖) (vecCons f φ)) := by
    rwa [← chartAbsDens_indicator_eq _ _ 0 (by simpa using hR)]
  rw [← integral_sub (integrable_chartDens hAf (hmeas _ hmU) hIU)
    (integrable_chartDens hAf (hmeas _ hmN) hIN)]
  obtain ⟨P, hP, hPy⟩ := LelongRegularise.exists_poly_of_linEval_eq_zero hJ hAf hu
  have hgood : ∀ᵐ y : Fin (d + 1) → ℂ, ∀ x ∈ fibre J hA.choose y, linEval u x ≠ 0 := by
    filter_upwards [LelongRegularise.ae_eval_ne_zero P hP] with y hy x hx hx0
    exact hy (hPy y x hx hx0)
  refine tendsto_integral_filter_of_dominated_convergence _ ?_ ?_ ((hI1.const_mul 2).add hI2) ?_
  · filter_upwards [self_mem_nhdsWithin] with ε _
    exact (hmeas _ (measurable_fsLogReg h u ε)).aestronglyMeasurable
  · filter_upwards [Ioc_mem_nhdsGT one_pos] with ε hε
    filter_upwards [hgood] with y hy
    exact norm_chartDens_fsLogReg_le h hAf φ hR h0 hε.1 hε.2 hy
  · filter_upwards [hgood] with y hy
    exact tendsto_chartDens_fsLogReg h hAf u _ h0 hy

end SliceFormLelongCompact

end

end GroundTheory.Heights₂.Heights
