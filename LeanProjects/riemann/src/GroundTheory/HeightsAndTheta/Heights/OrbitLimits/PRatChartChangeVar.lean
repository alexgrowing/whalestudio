import Mathlib
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StRatChartChangeVar
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StRatSheetSumMeasurable
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StRatSheetNoChartNull
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StChartSheetNoRatNull
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.StRatPosPartLocal
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PIntegralIndependent
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PPosPartSplit
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Matrix ComplexSets

namespace RatChartChangeVar

variable {n d : ℕ}

theorem ratDens_eq_posParts {J : Ideal (MvPolynomial (Fin n) ℂ)} {p : Fin d → MvPolynomial (Fin n) ℂ}
    {q : MvPolynomial (Fin n) ℂ} (f : (Fin n → ℂ) → ℝ) (φ : Fin d → (Fin n → ℂ) → ℝ) (y : Fin d → ℂ)
    (hfin : (RatChart.ratFibre J p q y).Finite) :
    RatChart.ratAbsDens J p q f φ y = RatChart.ratPosDens J p q f φ y + RatChart.ratPosDens J p q (-f) φ y ∧
      RatChart.ratDens J p q f φ y = RatChart.ratPosDens J p q f φ y - RatChart.ratPosDens J p q (-f) φ y := by
  unfold RatChart.ratAbsDens RatChart.ratDens RatChart.ratPosDens RatChart.ratSheetSum
  simp only [finsum_mem_eq_finite_toFinset_sum _ hfin, ← Finset.sum_add_distrib,
    ← Finset.sum_sub_distrib]
  refine ⟨Finset.sum_congr rfl fun x _ => ?_, Finset.sum_congr rfl fun x _ => ?_⟩ <;>
    split_ifs <;> simp only [Pi.neg_apply, neg_mul, max_zero_add_max_neg_zero_eq_abs_self,
      max_zero_sub_max_neg_zero_eq_self, add_zero, sub_zero]

theorem ratPosDens_nonneg (J : Ideal (MvPolynomial (Fin n) ℂ)) (p : Fin d → MvPolynomial (Fin n) ℂ)
    (q : MvPolynomial (Fin n) ℂ) (f : (Fin n → ℂ) → ℝ) (φ : Fin d → (Fin n → ℂ) → ℝ) (y : Fin d → ℂ) :
    0 ≤ RatChart.ratPosDens J p q f φ y := by
  unfold RatChart.ratPosDens RatChart.ratSheetSum
  exact finsum_nonneg fun x => finsum_nonneg fun _ => by split_ifs <;> simp

theorem measurable_ratPosDens (hM : RatSheetSumMeasurable.Statement) {J : Ideal (MvPolynomial (Fin n) ℂ)}
    {p : Fin d → MvPolynomial (Fin n) ℂ} {q : MvPolynomial (Fin n) ℂ}
    (hfin : ∀ y, (RatChart.ratFibre J p q y).Finite) {f : (Fin n → ℂ) → ℝ} (hf : Measurable f)
    (φ : Fin d → (Fin n → ℂ) → ℝ) : Measurable (RatChart.ratPosDens J p q f φ) :=
  hM n d J p q (fun a b => max (a * b) 0) f φ hfin
    ((continuous_fst.mul continuous_snd).max continuous_const).measurable hf

theorem ratInt_eq_posParts (hM : RatSheetSumMeasurable.Statement) {J : Ideal (MvPolynomial (Fin n) ℂ)}
    {p : Fin d → MvPolynomial (Fin n) ℂ} {q : MvPolynomial (Fin n) ℂ}
    (hfin : ∀ y, (RatChart.ratFibre J p q y).Finite) {f : (Fin n → ℂ) → ℝ} (hf : Measurable f)
    (φ : Fin d → (Fin n → ℂ) → ℝ) :
    (Integrable (RatChart.ratAbsDens J p q f φ) ↔
      (∫⁻ y, ENNReal.ofReal (RatChart.ratPosDens J p q f φ y)) +
        ∫⁻ y, ENNReal.ofReal (RatChart.ratPosDens J p q (-f) φ y) < ⊤) ∧
    (Integrable (RatChart.ratAbsDens J p q f φ) → ∫ y, RatChart.ratDens J p q f φ y =
      (∫⁻ y, ENNReal.ofReal (RatChart.ratPosDens J p q f φ y)).toReal -
        (∫⁻ y, ENNReal.ofReal (RatChart.ratPosDens J p q (-f) φ y)).toReal) := by
  have h0 := ratPosDens_nonneg J p q f φ
  have h1 := ratPosDens_nonneg J p q (-f) φ
  have m0 := measurable_ratPosDens hM hfin hf φ
  have m1 := measurable_ratPosDens hM hfin hf.neg φ
  have habs : RatChart.ratAbsDens J p q f φ =
      fun y => RatChart.ratPosDens J p q f φ y + RatChart.ratPosDens J p q (-f) φ y :=
    funext fun y => (ratDens_eq_posParts f φ y (hfin y)).1
  have hlin : ∫⁻ y, ENNReal.ofReal (RatChart.ratAbsDens J p q f φ y) =
      (∫⁻ y, ENNReal.ofReal (RatChart.ratPosDens J p q f φ y)) +
        ∫⁻ y, ENNReal.ofReal (RatChart.ratPosDens J p q (-f) φ y) := by
    rw [habs, ← lintegral_add_left m0.ennreal_ofReal]
    exact lintegral_congr fun y => ENNReal.ofReal_add (h0 y) (h1 y)
  have hint : Integrable (RatChart.ratAbsDens J p q f φ) ↔
      ∫⁻ y, ENNReal.ofReal (RatChart.ratAbsDens J p q f φ y) < ⊤ := by
    rw [habs, Integrable, hasFiniteIntegral_iff_ofReal
      (Filter.Eventually.of_forall fun y => add_nonneg (h0 y) (h1 y))]
    exact and_iff_right (m0.add m1).aestronglyMeasurable
  refine ⟨hint.trans (by rw [hlin]), fun hi => ?_⟩
  have hi0 : Integrable (RatChart.ratPosDens J p q f φ) := hi.mono' m0.aestronglyMeasurable
    (Filter.Eventually.of_forall fun y => by
      rw [Real.norm_of_nonneg (h0 y), habs]; linarith [h1 y])
  have hi1 : Integrable (RatChart.ratPosDens J p q (-f) φ) := hi.mono' m1.aestronglyMeasurable
    (Filter.Eventually.of_forall fun y => by
      rw [Real.norm_of_nonneg (h1 y), habs]; linarith [h0 y])
  have hd : RatChart.ratDens J p q f φ =
      fun y => RatChart.ratPosDens J p q f φ y - RatChart.ratPosDens J p q (-f) φ y :=
    funext fun y => (ratDens_eq_posParts f φ y (hfin y)).2
  rw [hd, integral_sub hi0 hi1,
    integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall h0) m0.aestronglyMeasurable,
    integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall h1) m1.aestronglyMeasurable]

theorem ratPosDens_split {J : Ideal (MvPolynomial (Fin n) ℂ)} {p : Fin d → MvPolynomial (Fin n) ℂ}
    {q : MvPolynomial (Fin n) ℂ} (f : (Fin n → ℂ) → ℝ) (φ : Fin d → (Fin n → ℂ) → ℝ)
    (E : ℕ → Set (Fin n → ℂ)) (y : Fin d → ℂ) (hfin : (RatChart.ratFibre J p q y).Finite)
    (hE : Pairwise (Function.onFun Disjoint E))
    (hcov : ∀ x ∈ RatChart.ratFibre J p q y, (∃ s, RatChart.IsRatSheetAt J p q x s) → ∃ k, x ∈ E k) :
    ENNReal.ofReal (RatChart.ratPosDens J p q f φ y) =
      ∑' k, ENNReal.ofReal (RatChart.ratPosDens J p q ((E k).indicator f) φ y) := by
  classical
  unfold RatChart.ratPosDens RatChart.ratSheetSum
  simp only [finsum_mem_eq_finite_toFinset_sum _ hfin]
  set T : ((Fin n → ℂ) → ℝ) → (Fin n → ℂ) → ℝ := fun g x =>
    if h : ∃ s, RatChart.IsRatSheetAt J p q x s then
      max (g x * ReciprocityTheory.AnForm.maDens (fun k => φ k ∘ h.choose) y) 0 else 0 with hT
  have hT0 : ∀ g x, 0 ≤ T g x := fun g x => by
    simp only [hT]; split_ifs <;> simp
  have hpt : ∀ x ∈ hfin.toFinset,
      ENNReal.ofReal (T f x) = ∑' k, ENNReal.ofReal (T ((E k).indicator f) x) := by
    intro x hx
    have hx' : x ∈ RatChart.ratFibre J p q y := hfin.mem_toFinset.mp hx
    by_cases hs : ∃ s, RatChart.IsRatSheetAt J p q x s
    · obtain ⟨k₀, hk₀⟩ := hcov x hx' hs
      rw [tsum_eq_single k₀]
      · simp only [hT, dif_pos hs, Set.indicator_of_mem hk₀]
      · intro k hk
        have hxk : x ∉ E k := fun hxk => Set.disjoint_left.mp (hE hk) hxk hk₀
        simp [hT, dif_pos hs, Set.indicator_of_notMem hxk]
    · simp [hT, dif_neg hs]
  rw [ENNReal.ofReal_sum_of_nonneg (fun x _ => hT0 f x), Finset.sum_congr rfl hpt,
    ← Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)]
  exact tsum_congr fun k => (ENNReal.ofReal_sum_of_nonneg (fun x _ => hT0 _ x)).symm

theorem posPart_eq (hM : RatSheetSumMeasurable.Statement) (hN1 : RatSheetNoChartNull.Statement)
    (hN2 : ChartSheetNoRatNull.Statement) (hL : RatPosPartLocal.Statement)
    {J : Ideal (MvPolynomial (Fin n) ℂ)} {A : Matrix (Fin d) (Fin n) ℂ}
    {p : Fin d → MvPolynomial (Fin n) ℂ} {q : MvPolynomial (Fin n) ℂ}
    {f : (Fin n → ℂ) → ℝ} {φ : Fin d → (Fin n → ℂ) → ℝ}
    (hJ : J.IsPrime) (hd : ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = d) (hA : IsFiniteProjection J A)
    (hq : q ∉ J) (hfin : ∀ y, (RatChart.ratFibre J p q y).Finite) (hf : Measurable f)
    (hφ : ∀ k, SmoothNear (zeroSet J) (φ k)) :
    ∫⁻ y, ENNReal.ofReal (RatChart.ratPosDens J p q f φ y) =
      ∫⁻ y, ENNReal.ofReal (chartPosDens J A f φ y) := by

  have key : ∀ x : Fin n → ℂ, ∃ W : Set (Fin n → ℂ), IsOpen W ∧
      ((∃ s, IsSheetAt J A x s) → (∃ s', RatChart.IsRatSheetAt J p q x s') → x ∈ W) ∧
      ∀ E : Set (Fin n → ℂ), MeasurableSet E → E ⊆ W →
        ∫⁻ y, ENNReal.ofReal (RatChart.ratPosDens J p q (E.indicator f) φ y) =
          ∫⁻ y, ENNReal.ofReal (chartPosDens J A (E.indicator f) φ y) := by
    intro x
    by_cases hx : (∃ s, IsSheetAt J A x s) ∧ ∃ s', RatChart.IsRatSheetAt J p q x s'
    · obtain ⟨W, hW, hxW, hWE⟩ := hL n d J A p q f φ x hf hφ hx.1 hx.2
      exact ⟨W, hW, fun _ _ => hxW, fun E hE hEW => (hWE E hE hEW).symm⟩
    · refine ⟨∅, isOpen_empty, fun h1 h2 => absurd ⟨h1, h2⟩ hx, fun E _ hE => ?_⟩
      rw [Set.subset_empty_iff.1 hE, Set.indicator_empty]
      simp [chartPosDens, sheetSum, RatChart.ratPosDens, RatChart.ratSheetSum]
  choose W hWo hxW hWE using key
  obtain ⟨T, hTc, hTU⟩ := TopologicalSpace.isOpen_iUnion_countable W hWo
  obtain ⟨e, he⟩ := (hTc.insert 0).exists_eq_range (Set.insert_nonempty 0 T)
  set E : ℕ → Set (Fin n → ℂ) := fun k => zeroSet J ∩ disjointed (fun k => W (e k)) k with hE
  have hEm : ∀ k, MeasurableSet (E k) := fun k =>
    (SheetSumMeasurable.isClosed_zeroSet J).measurableSet.inter
      (MeasurableSet.disjointed (fun k => (hWo (e k)).measurableSet) k)
  have hEW : ∀ k, E k ⊆ W (e k) := fun k x hx => disjointed_subset (fun k => W (e k)) k hx.2
  have hEd : Pairwise (Function.onFun Disjoint E) := fun i j hij =>
    ((disjoint_disjointed (fun k => W (e k))) hij).mono Set.inter_subset_right
      Set.inter_subset_right
  have hcov : ∀ x ∈ zeroSet J, (∃ s, IsSheetAt J A x s) → (∃ s', RatChart.IsRatSheetAt J p q x s') →
      ∃ k, x ∈ E k := by
    intro x hxZ h1 h2
    have : x ∈ ⋃ i ∈ T, W i := hTU ▸ Set.mem_iUnion.2 ⟨x, hxW x h1 h2⟩
    obtain ⟨i, hiT, hxi⟩ := Set.mem_iUnion₂.1 this
    obtain ⟨m, rfl⟩ : i ∈ Set.range e := he ▸ Set.mem_insert_of_mem 0 hiT
    have : x ∈ ⋃ k, disjointed (fun k => W (e k)) k := by
      rw [iUnion_disjointed]
      exact Set.mem_iUnion.2 ⟨m, hxi⟩
    obtain ⟨k, hk⟩ := Set.mem_iUnion.1 this
    exact ⟨k, hxZ, hk⟩

  have haeR : ∀ᵐ y, ENNReal.ofReal (RatChart.ratPosDens J p q f φ y) =
      ∑' k, ENNReal.ofReal (RatChart.ratPosDens J p q ((E k).indicator f) φ y) := by
    filter_upwards [measure_eq_zero_iff_ae_notMem.1 (hN1 n d J A p q hJ hd hA hfin)] with y hy
    refine ratPosDens_split f φ E y (hfin y) hEd fun x hx hs => hcov x hx.1 ?_ hs
    by_contra hn
    exact hy ⟨x, ⟨hx.1, hs, hn⟩, hx.2.2⟩
  have haeA : ∀ᵐ y, ENNReal.ofReal (chartPosDens J A f φ y) =
      ∑' k, ENNReal.ofReal (chartPosDens J A ((E k).indicator f) φ y) := by
    filter_upwards [measure_eq_zero_iff_ae_notMem.1 (hN2 n d J A p q hJ hd hA hq hfin)] with y hy
    refine PosPartSplit.proof n d J A f φ E y hA hEd fun x hx hs => hcov x hx.1 hs ?_
    by_contra hn
    exact hy ⟨x, ⟨hx.1, hs, hn⟩, hx.2⟩
  rw [lintegral_congr_ae haeR, lintegral_congr_ae haeA,
    lintegral_tsum fun k => (measurable_ratPosDens hM hfin (hf.indicator (hEm k)) φ).ennreal_ofReal.aemeasurable,
    lintegral_tsum fun k =>
      (IntegralIndep.measurable_chartPosDens hA (hf.indicator (hEm k)) φ).ennreal_ofReal.aemeasurable]
  exact tsum_congr fun k => hWE (e k) (E k) (hEm k) (hEW k)

end RatChartChangeVar

theorem RatChartChangeVar.proof (hM : RatSheetSumMeasurable.Statement) (hN1 : RatSheetNoChartNull.Statement)
    (hN2 : ChartSheetNoRatNull.Statement) (hL : RatPosPartLocal.Statement) :
    RatChartChangeVar.Statement := by
  intro n d J A p q f φ hJ hd hA hq hfin hf hφ
  have m1 : Measurable (RatChart.ratDens J p q f φ) :=
    hM n d J p q (fun a b => a * b) f φ hfin (continuous_fst.mul continuous_snd).measurable hf
  have m2 : Measurable (RatChart.ratAbsDens J p q f φ) :=
    hM n d J p q (fun a b => |a * b|) f φ hfin (continuous_fst.mul continuous_snd).abs.measurable hf
  refine ⟨m1.aestronglyMeasurable, m2.aestronglyMeasurable, fun hi => ?_⟩
  have e0 := RatChartChangeVar.posPart_eq hM hN1 hN2 hL hJ hd hA hq hfin hf hφ
  have e1 := RatChartChangeVar.posPart_eq hM hN1 hN2 hL hJ hd hA hq hfin hf.neg hφ
  obtain ⟨iR, cR⟩ := RatChartChangeVar.ratInt_eq_posParts hM hfin hf φ
  obtain ⟨iA, cA⟩ := IntegralIndep.chartInt_eq_posParts hA hf φ
  have hi' : Integrable (chartAbsDens J A f φ) := iA.2 (by rw [← e0, ← e1]; exact iR.1 hi)
  exact ⟨hi', by rw [cR hi, cA hi', e0, e1]⟩

end GroundTheory.Heights₂.Heights
