import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IndicatorIntMMemSB
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.SplitFlip GlobalTheory.KSplit Classical
open scoped ENNReal

namespace GlobalTheory.KSplit

section OneVar

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem absPow_mul_of_ne_zero {s : ℝ} (hs : s < 0) {a : k} (ha : a ≠ 0) (y : k) :
    ENNReal.ofReal (if h : a * y = 0 then 0 else nabs k (Units.mk0 (a * y) h)) ^ s =
      ENNReal.ofReal (nabs k (Units.mk0 a ha)) ^ s *
        ENNReal.ofReal (if h : y = 0 then 0 else nabs k (Units.mk0 y h)) ^ s := by
  have hpa : ENNReal.ofReal (nabs k (Units.mk0 a ha)) ≠ 0 := by
    simpa using Model.nabs_pos _
  by_cases hy : y = 0
  · subst hy
    have : ENNReal.ofReal (nabs k (Units.mk0 a ha)) ^ s ≠ 0 := by
      simp [ENNReal.rpow_eq_zero_iff, hpa]
    simp [ENNReal.zero_rpow_of_neg hs, ENNReal.mul_top this]
  · have hay : a * y ≠ 0 := mul_ne_zero ha hy
    have hpy : ENNReal.ofReal (nabs k (Units.mk0 y hy)) ≠ 0 := by
      simpa using Model.nabs_pos _
    have e : Units.mk0 (a * y) hay = Units.mk0 a ha * Units.mk0 y hy := Units.ext rfl
    rw [dif_neg hay, dif_neg hy, e, Model.nabs_mul, ENNReal.ofReal_mul (Model.nabs_pos _).le,
      ENNReal.mul_rpow_of_ne_zero hpa hpy]

theorem absPow_le_one_of_notMem [MeasurableSpace k] [BorelSpace k] {s : ℝ} (hs : s < 0) {y : k} (hy : y ∉ 𝒪[k]) :
    ENNReal.ofReal (if h : y = 0 then 0 else nabs k (Units.mk0 y h)) ^ s ≤ 1 := by
  have h0 : y ≠ 0 := fun h => hy (h ▸ zero_mem _)
  rw [dif_neg h0]
  refine ENNReal.rpow_le_one_of_one_le_of_neg ?_ hs
  have h1 : valuation k y⁻¹ ≤ 1 := ((valuation k).val_le_one_or_val_inv_le_one y).resolve_left hy
  have h2 : nabs k (Units.mk0 y h0)⁻¹ ≤ 1 := Model.nabs_le_one _ (by simpa using h1)
  have h3 : nabs k (Units.mk0 y h0) * nabs k (Units.mk0 y h0)⁻¹ = 1 := by
    rw [← Model.nabs_mul, mul_inv_cancel, Model.nabs_one]
  have h4 := Model.nabs_pos (Units.mk0 y h0)
  rw [ENNReal.one_le_ofReal]
  nlinarith

end OneVar

theorem lintegral_absPow_affine_le (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (μ : Measure k) [μ.IsAddHaarMeasure] (s : ℝ)
    (hs : s < 0) (a b : k) :
    ∫⁻ x, (𝒪[k] : Set k).indicator (fun y => ENNReal.ofReal (if h : a * y + b = 0 then 0 else nabs k (Units.mk0 (a * y + b) h)) ^ s) x ∂μ ≤
      ENNReal.ofReal (if h : a = 0 then 0 else nabs k (Units.mk0 a h)) ^ s *
        (∫⁻ x, (𝒪[k] : Set k).indicator (fun y => ENNReal.ofReal (if h : y = 0 then 0 else nabs k (Units.mk0 y h)) ^ s) x ∂μ + μ (𝒪[k] : Set k)) := by
  have hO : IsOpen (𝒪[k] : Set k) := Model.isOpen_int
  by_cases ha : a = 0
  · have hpos : μ (𝒪[k] : Set k) ≠ 0 := (hO.measure_pos μ ⟨0, zero_mem _⟩).ne'
    rw [dif_pos ha, ENNReal.ofReal_zero, ENNReal.zero_rpow_of_neg hs, ENNReal.top_mul]
    · exact le_top
    · exact fun h => hpos (add_eq_zero.1 h).2
  rw [dif_neg ha]
  set P : k → ℝ≥0∞ := fun y => ENNReal.ofReal (if h : y = 0 then 0 else nabs k (Units.mk0 y h)) ^ s with hP
  set C : ℝ≥0∞ := ENNReal.ofReal (nabs k (Units.mk0 a ha)) ^ s with hC
  have hCt : C ≠ ⊤ := by
    have hpa : ENNReal.ofReal (nabs k (Units.mk0 a ha)) ≠ 0 := by
      simpa using Model.nabs_pos _
    simp [hC, ENNReal.rpow_eq_top_iff, hpa]
  have hpt : ∀ x, (𝒪[k] : Set k).indicator (fun y => P (a * y + b)) x ≤
      C * ((𝒪[k] : Set k).indicator P (x + b / a) + (𝒪[k] : Set k).indicator 1 x) := by
    intro x
    by_cases hx : x ∈ (𝒪[k] : Set k)
    · rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx]
      have e : a * x + b = a * (x + b / a) := by field_simp
      have e' : P (a * x + b) = C * P (x + b / a) := by
        rw [e]; exact absPow_mul_of_ne_zero hs ha _
      rw [e']
      gcongr
      by_cases hx' : x + b / a ∈ (𝒪[k] : Set k)
      · rw [Set.indicator_of_mem hx']; exact le_self_add
      · rw [Set.indicator_of_notMem hx', zero_add]; exact absPow_le_one_of_notMem hs hx'
    · rw [Set.indicator_of_notMem hx]; exact zero_le
  calc _ ≤ ∫⁻ x, C * ((𝒪[k] : Set k).indicator P (x + b / a) + (𝒪[k] : Set k).indicator 1 x) ∂μ :=
        lintegral_mono hpt
    _ = _ := by
        rw [lintegral_const_mul' _ _ hCt,
          lintegral_add_right _ (measurable_one.indicator hO.measurableSet),
          lintegral_add_right_eq_self (fun x => (𝒪[k] : Set k).indicator P x),
          lintegral_indicator_one hO.measurableSet]

end GlobalTheory.KSplit
