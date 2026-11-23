import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StSheetAreaCompare
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StSheetImageArea
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PSheetSumMeasurable
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PProjectionFormula
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.IsAddHaarMeasureHausdorffMeasureEuclideanSpaceCo
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory Filter Topology Matrix ComplexSets

open scoped ENNReal

noncomputable section

namespace SheetAreaCompare

variable {n d : ℕ}

theorem measurable_sheetJac (s : (Fin d → ℂ) → Fin n → ℂ) : Measurable (sheetJac s) := by
  let φ : EuclideanSpace ℂ (Fin d) →L[ℝ] (Fin d → ℂ) :=
    (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin d => ℂ)).toContinuousLinearMap
  let ψ : (Fin n → ℂ) →L[ℝ] EuclideanSpace ℂ (Fin n) :=
    (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin n => ℂ)).symm.toContinuousLinearMap
  have h : sheetJac s = (fun M : EuclideanSpace ℂ (Fin d) →L[ℝ] EuclideanSpace ℂ (Fin n) =>
      areaJacobian (M : EuclideanSpace ℂ (Fin d) →ₗ[ℝ] EuclideanSpace ℂ (Fin n))) ∘
        (fun L : (Fin d → ℂ) →L[ℝ] (Fin n → ℂ) => ψ.comp (L.comp φ)) ∘ fderiv ℝ s := by
    funext y
    rfl
  rw [h]
  have hc : Continuous fun L : (Fin d → ℂ) →L[ℝ] (Fin n → ℂ) => ψ.comp (L.comp φ) := by fun_prop
  exact continuous_areaJacobian.measurable.comp (hc.measurable.comp (measurable_fderiv ℝ s))

theorem exists_lintegral_volume_eq (d : ℕ) : ∃ c : NNReal, ∀ F : (Fin d → ℂ) → ℝ≥0∞,
    ∫⁻ y, F y = c * ∫⁻ y, F (WithLp.ofLp y)
      ∂(μH[((2 * d : ℕ) : ℝ)] : Measure (EuclideanSpace ℂ (Fin d))) := by
  let e := (EuclideanSpace.equiv (Fin d) ℂ).toHomeomorph.toMeasurableEquiv
  let ν : Measure (Fin d → ℂ) := (μH[((2 * d : ℕ) : ℝ)] : Measure (EuclideanSpace ℂ (Fin d))).map e
  have : ν.IsAddHaarMeasure := (EuclideanSpace.equiv (Fin d) ℂ).isAddHaarMeasure_map _
  refine ⟨Measure.addHaarScalarFactor volume ν, fun F => ?_⟩
  conv_lhs => rw [Measure.isAddLeftInvariant_eq_smul volume ν]
  rw [lintegral_smul_measure, lintegral_map_equiv F e]
  rfl

theorem ofReal_finsum_le_tsum {α : Type*} (f : α → ℝ) (hf : ∀ a, 0 ≤ f a) :
    ENNReal.ofReal (∑ᶠ a, f a) ≤ ∑' a, ENNReal.ofReal (f a) := by
  by_cases h : (Function.support f).Finite
  · rw [finsum_eq_sum f h, ENNReal.ofReal_sum_of_nonneg fun a _ => hf a]
    exact ENNReal.sum_le_tsum _
  · rw [finsum_of_infinite_support h]
    simp

theorem exists_sheet_nhds {J : Ideal (MvPolynomial (Fin n) ℂ)} {A : Matrix (Fin d) (Fin n) ℂ}
    (x : Fin n → ℂ) :
    ∃ (s : (Fin d → ℂ) → Fin n → ℂ) (U : Set (Fin d → ℂ)) (W : Set (Fin n → ℂ)),
      IsOpen U ∧ IsOpen W ∧ DifferentiableOn ℂ s U ∧ (∀ y ∈ U, A *ᵥ s y = y ∧ s y ∈ zeroSet J) ∧
      (∀ x' ∈ zeroSet J ∩ W, A *ᵥ x' ∈ U ∧ IsSheetAt J A x' s) ∧
      ((∃ s, IsSheetAt J A x s) → x ∈ W) := by
  by_cases hx : ∃ s, IsSheetAt J A x s
  · obtain ⟨s, U, hU, hxU, hsd, hsx, hsec, V, hV, hVs⟩ := hx
    have hAc : Continuous fun z : Fin n → ℂ => A *ᵥ z := by fun_prop
    refine ⟨s, U, interior V ∩ (fun z => A *ᵥ z) ⁻¹' U, hU,
      isOpen_interior.inter (hU.preimage hAc), hsd, hsec, ?_, fun _ =>
        ⟨mem_interior_iff_mem_nhds.2 hV, hxU⟩⟩
    rintro x' ⟨hx'Z, hx'V, hx'U⟩
    have hx's : s (A *ᵥ x') = x' := (hVs x' ⟨hx'Z, interior_subset hx'V⟩ hx'U).symm
    exact ⟨hx'U, U, hU, hx'U, hsd, hx's, hsec, interior V, isOpen_interior.mem_nhds hx'V,
      fun x'' hx'' hAx'' => hVs x'' ⟨hx''.1, interior_subset hx''.2⟩ hAx''⟩
  · exact ⟨fun _ => x, ∅, ∅, isOpen_empty, isOpen_empty, differentiableOn_empty, by simp,
      by simp, fun h => absurd h hx⟩

end SheetAreaCompare

open SheetAreaCompare in

theorem SheetAreaCompare.proof (h₁ : SheetImageArea.Statement) : SheetAreaCompare.Statement := by
  classical
  intro n d J A
  obtain ⟨c, hc⟩ := exists_lintegral_volume_eq d
  refine ⟨c, ENNReal.coe_lt_top, fun h hh => ?_⟩
  choose σ U W hU hW hσd hσsec hWsh hxW using
    fun x : Fin n → ℂ => exists_sheet_nhds (J := J) (A := A) x

  obtain ⟨T, hTc, hTU⟩ := TopologicalSpace.isOpen_iUnion_countable W hW
  obtain ⟨e, he⟩ := (hTc.insert 0).exists_eq_range (Set.insert_nonempty 0 T)
  have hcover : ∀ x, (∃ s, IsSheetAt J A x s) → ∃ k, x ∈ W (e k) := by
    intro x hx
    have : x ∈ ⋃ i ∈ T, W i := hTU ▸ Set.mem_iUnion.2 ⟨x, hxW x hx⟩
    obtain ⟨i, hiT, hxi⟩ := Set.mem_iUnion₂.1 this
    obtain ⟨k, rfl⟩ : i ∈ Set.range e := he ▸ Set.mem_insert_of_mem 0 hiT
    exact ⟨k, hxi⟩

  set E : ℕ → Set (Fin n → ℂ) := fun k => zeroSet J ∩ disjointed (fun k => W (e k)) k with hE
  have hEm : ∀ k, MeasurableSet (E k) := fun k =>
    (SheetSumMeasurable.isClosed_zeroSet J).measurableSet.inter
      (MeasurableSet.disjointed (fun k => (hW (e k)).measurableSet) k)
  have hEW : ∀ k, E k ⊆ zeroSet J ∩ W (e k) := fun k x hx =>
    ⟨hx.1, disjointed_subset (fun k => W (e k)) k hx.2⟩
  have hEdisj : Pairwise fun k k' => Disjoint (E k) (E k') := fun k k' hkk' =>
    (disjoint_disjointed (fun k => W (e k)) hkk').mono Set.inter_subset_right Set.inter_subset_right
  have hEcover : ∀ x, (∃ s, IsSheetAt J A x s) → ∃ k, x ∈ E k := by
    intro x hx
    obtain ⟨m, hm⟩ := hcover x hx
    have hxZ : x ∈ zeroSet J := by
      obtain ⟨s, U₀, -, hxU₀, -, hsx, hsec, -⟩ := hx
      rw [← hsx]
      exact (hsec _ hxU₀).2
    have : x ∈ ⋃ k, disjointed (fun k => W (e k)) k := by
      rw [iUnion_disjointed]
      exact Set.mem_iUnion.2 ⟨m, hm⟩
    obtain ⟨k, hk⟩ := Set.mem_iUnion.1 this
    exact ⟨k, hxZ, hk⟩

  set σ' : ℕ → (Fin d → ℂ) → Fin n → ℂ := fun k => (U (e k)).piecewise (σ (e k)) fun _ => 0
    with hσ'
  have hσ'm : ∀ k, Measurable (σ' k) := fun k =>
    (hσd (e k)).continuousOn.measurable_piecewise continuousOn_const (hU (e k)).measurableSet
  have hσ'eq : ∀ k, ∀ y ∈ U (e k), σ' k y = σ (e k) y := fun k y hy => by
    simp [hσ', Set.piecewise_eq_of_mem _ _ _ hy]
  set B : ℕ → Set (Fin d → ℂ) := fun k => U (e k) ∩ σ' k ⁻¹' E k with hB
  have hBm : ∀ k, MeasurableSet (B k) := fun k =>
    (hU (e k)).measurableSet.inter (hσ'm k (hEm k))
  have hBmem : ∀ k y, y ∈ B k ↔ y ∈ U (e k) ∧ σ (e k) y ∈ E k := by
    intro k y
    constructor
    · rintro ⟨hy, hy'⟩
      exact ⟨hy, by simpa [Set.mem_preimage, hσ'eq k y hy] using hy'⟩
    · rintro ⟨hy, hy'⟩
      exact ⟨hy, by simpa [Set.mem_preimage, hσ'eq k y hy] using hy'⟩
  set G : ℕ → (Fin d → ℂ) → ℝ≥0∞ := fun k y =>
    ‖h (σ' k y)‖ₑ * ENNReal.ofReal (sheetJac (σ (e k)) y) with hG
  have hGm : ∀ k, Measurable (G k) := fun k =>
    (hh.comp (hσ'm k)).enorm.mul (ENNReal.measurable_ofReal.comp (measurable_sheetJac _))

  set t : (Fin n → ℂ) → ℝ := fun x => if hx : ∃ s, IsSheetAt J A x s then
    |h x| * sheetJac hx.choose (A *ᵥ x) else 0 with ht
  have ht0 : ∀ x, 0 ≤ t x := by
    intro x
    simp only [ht]
    split_ifs
    · exact mul_nonneg (abs_nonneg _) (sheetJac_nonneg _ _)
    · exact le_rfl
  have htE : ∀ k x, x ∈ E k →
      ENNReal.ofReal (t x) = G k (A *ᵥ x) ∧ A *ᵥ x ∈ B k ∧ σ (e k) (A *ᵥ x) = x := by
    intro k x hx
    obtain ⟨hAU, hsh⟩ := hWsh (e k) x (hEW k hx)
    have hsx : σ (e k) (A *ᵥ x) = x := by
      obtain ⟨-, -, -, -, hsx, -⟩ := hsh
      exact hsx
    have hex : ∃ s, IsSheetAt J A x s := ⟨_, hsh⟩
    have hJ : sheetJac hex.choose (A *ᵥ x) = sheetJac (σ (e k)) (A *ᵥ x) := by
      unfold sheetJac
      rw [(SheetSumMeasurable.sheet_eventuallyEq hsh hex.choose_spec).fderiv_eq]
    refine ⟨?_, (hBmem k _).2 ⟨hAU, hsx.symm ▸ hx⟩, hsx⟩
    simp only [ht, dif_pos hex, hG, hσ'eq k _ hAU, hsx, hJ]
    rw [ENNReal.ofReal_mul (abs_nonneg _), Real.enorm_eq_ofReal_abs]

  have hpt : ∀ y, ‖sheetSum J A (fun x s => |h x| * sheetJac s (A *ᵥ x)) y‖ₑ ≤
      ∑' k, (B k).indicator (G k) y := by
    intro y
    have hS : sheetSum J A (fun x s => |h x| * sheetJac s (A *ᵥ x)) y =
        ∑ᶠ x, (fibre J A y).indicator t x := by
      unfold sheetSum
      rw [finsum_mem_def]
    have hnn : ∀ x, 0 ≤ (fibre J A y).indicator t x := fun x =>
      Set.indicator_nonneg (fun x _ => ht0 x) x
    rw [hS, Real.enorm_eq_ofReal (finsum_nonneg hnn)]
    calc ENNReal.ofReal (∑ᶠ x, (fibre J A y).indicator t x)
        ≤ ∑' x, ENNReal.ofReal ((fibre J A y).indicator t x) := ofReal_finsum_le_tsum _ hnn
      _ ≤ ∑' x, ∑' k, (E k ∩ fibre J A y).indicator (fun x => ENNReal.ofReal (t x)) x := by
        refine ENNReal.tsum_le_tsum fun x => ?_
        by_cases hxf : x ∈ fibre J A y
        · by_cases hx : ∃ s, IsSheetAt J A x s
          · obtain ⟨k, hk⟩ := hEcover x hx
            rw [Set.indicator_of_mem hxf]
            exact (Set.indicator_of_mem (show x ∈ E k ∩ fibre J A y from ⟨hk, hxf⟩)
              (fun x => ENNReal.ofReal (t x))).symm.le.trans (ENNReal.le_tsum k)
          · have : t x = 0 := by simp only [ht, dif_neg hx]
            rw [Set.indicator_of_mem hxf, this, ENNReal.ofReal_zero]
            exact zero_le
        · rw [Set.indicator_of_notMem hxf, ENNReal.ofReal_zero]
          exact zero_le
      _ = ∑' k, ∑' x, (E k ∩ fibre J A y).indicator (fun x => ENNReal.ofReal (t x)) x :=
        ENNReal.tsum_comm
      _ ≤ ∑' k, (B k).indicator (G k) y := by
        refine ENNReal.tsum_le_tsum fun k => ?_
        rw [tsum_eq_single (σ (e k) y)]
        · by_cases hm : σ (e k) y ∈ E k ∩ fibre J A y
          · rw [Set.indicator_of_mem hm]
            obtain ⟨h1, h2, -⟩ := htE k _ hm.1
            have hAy : A *ᵥ σ (e k) y = y := hm.2.2
            rw [hAy] at h1 h2
            rw [h1, Set.indicator_of_mem h2]
          · rw [Set.indicator_of_notMem hm]
            exact zero_le
        · intro x hne
          refine Set.indicator_of_notMem (fun hx => hne ?_) _
          obtain ⟨-, -, hsx⟩ := htE k x hx.1
          have hAx : A *ᵥ x = y := hx.2.2
          rw [← hAx, hsx]

  have hpiece : ∀ k, ∫⁻ y, (B k).indicator (G k) y = c * ∫⁻ z in (WithLp.ofLp ⁻¹' E k : Set (EuclideanSpace ℂ (Fin n))),
      ‖h (WithLp.ofLp z)‖ₑ ∂(μH[((2 * d : ℕ) : ℝ)]) := by
    intro k
    have hBm' : MeasurableSet (WithLp.ofLp ⁻¹' B k : Set (EuclideanSpace ℂ (Fin d))) :=
      (EuclideanSpace.equiv (Fin d) ℂ).continuous.measurable (hBm k)
    rw [hc]
    congr 1
    have h2 := h₁ n d A (U (e k)) (σ (e k)) (hU (e k)) (hσd (e k)) (fun y hy => (hσsec (e k) y hy).1)
      (WithLp.ofLp ⁻¹' B k) hBm' (fun y hy => hy.1) (fun z => ‖h (WithLp.ofLp z)‖ₑ)
      (hh.comp (EuclideanSpace.equiv (Fin n) ℂ).continuous.measurable).enorm
    have himg : (fun y : EuclideanSpace ℂ (Fin d) => WithLp.toLp 2 (σ (e k) (WithLp.ofLp y))) ''
        (WithLp.ofLp ⁻¹' B k) = WithLp.ofLp ⁻¹' E k := by
      ext z
      constructor
      · rintro ⟨y, hy, rfl⟩
        exact ((hBmem k _).1 hy).2
      · intro hz
        obtain ⟨-, h2, h3⟩ := htE k _ hz
        exact ⟨WithLp.toLp 2 (A *ᵥ WithLp.ofLp z), h2, by simp [h3]⟩
    rw [himg] at h2
    rw [← h2, ← lintegral_indicator hBm']
    refine lintegral_congr fun y => ?_
    by_cases hy : y ∈ WithLp.ofLp ⁻¹' B k
    · rw [Set.indicator_of_mem hy, Set.indicator_of_mem (show WithLp.ofLp y ∈ B k from hy)]
      simp [hG, hσ'eq k _ hy.1]
    · rw [Set.indicator_of_notMem hy, Set.indicator_of_notMem (show WithLp.ofLp y ∉ B k from hy)]
  have hImeas : ∀ k, MeasurableSet (WithLp.ofLp ⁻¹' E k : Set (EuclideanSpace ℂ (Fin n))) :=
    fun k => (EuclideanSpace.equiv (Fin n) ℂ).continuous.measurable (hEm k)
  have hIdisj : Pairwise fun k k' => Disjoint (WithLp.ofLp ⁻¹' E k : Set (EuclideanSpace ℂ (Fin n)))
      (WithLp.ofLp ⁻¹' E k') :=
    fun k k' hkk' => (hEdisj hkk').preimage _
  have hIsub : (⋃ k, (WithLp.ofLp ⁻¹' E k : Set (EuclideanSpace ℂ (Fin n)))) ⊆ zeroSetEuc J := by
    intro z hz
    obtain ⟨k, hk⟩ := Set.mem_iUnion.1 hz
    intro q hq
    exact (hEW k hk).1 q hq
  calc ∫⁻ y, ‖sheetSum J A (fun x s => |h x| * sheetJac s (A *ᵥ x)) y‖ₑ
      ≤ ∫⁻ y, ∑' k, (B k).indicator (G k) y := lintegral_mono hpt
    _ = ∑' k, ∫⁻ y, (B k).indicator (G k) y :=
        lintegral_tsum fun k => ((hGm k).indicator (hBm k)).aemeasurable
    _ = c * ∫⁻ z in ⋃ k, (WithLp.ofLp ⁻¹' E k : Set (EuclideanSpace ℂ (Fin n))), ‖h (WithLp.ofLp z)‖ₑ ∂(μH[((2 * d : ℕ) : ℝ)]) := by
        rw [lintegral_iUnion hImeas hIdisj, ← ENNReal.tsum_mul_left]
        exact tsum_congr hpiece
    _ ≤ c * ∫⁻ z in zeroSetEuc J, ‖h (WithLp.ofLp z)‖ₑ ∂(μH[((2 * d : ℕ) : ℝ)]) :=
        mul_le_mul_of_nonneg_left (lintegral_mono_set hIsub) zero_le

end

end GroundTheory.Heights₂.Heights
