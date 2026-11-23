import Mathlib
open MeasureTheory
open scoped ComplexConjugate ENNReal

namespace GlobalTheory.AbsFubini

variable {X₁ X₂ Y : Type*} [MeasurableSpace X₁] [MeasurableSpace X₂] [MeasurableSpace Y]
  {μ₁ : Measure X₁} {μ₂ : Measure X₂} {ν : Measure Y} [SigmaFinite μ₁] [SigmaFinite μ₂] [SigmaFinite ν]

lemma lintegral_mul_le_sqrt (ν : Measure Y) {a₁ a₂ : Y → ℝ≥0∞} (h₁ : Measurable a₁) (h₂ : Measurable a₂) :
    ∫⁻ y, a₁ y * a₂ y ∂ν ≤
      (∫⁻ y, a₁ y ^ (2:ℝ) ∂ν) ^ (1 / (2:ℝ)) * (∫⁻ y, a₂ y ^ (2:ℝ) ∂ν) ^ (1 / (2:ℝ)) := by
  have h := ENNReal.lintegral_mul_le_Lp_mul_Lq ν Real.HolderConjugate.two_two h₁.aemeasurable
    h₂.aemeasurable
  simpa only [Pi.mul_apply] using h

lemma sqrt_le_of_sq_le {I N : ℝ≥0∞} (h : I ≤ N ^ 2) : I ^ (1 / (2:ℝ)) ≤ N := by
  calc I ^ (1 / (2:ℝ)) ≤ (N ^ 2) ^ (1 / (2:ℝ)) := ENNReal.rpow_le_rpow h (by norm_num)
    _ = N := by
      rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]; norm_num

lemma lintegral_prod_split {a₁ : X₁ → Y → ℝ≥0∞} {a₂ : X₂ → Y → ℝ≥0∞}
    (ha₁ : Measurable (Function.uncurry a₁)) (ha₂ : Measurable (Function.uncurry a₂)) (y : Y) :
    (∫⁻ x₁, a₁ x₁ y ∂μ₁) * (∫⁻ x₂, a₂ x₂ y ∂μ₂) = ∫⁻ p : X₁ × X₂, a₁ p.1 y * a₂ p.2 y ∂μ₁.prod μ₂ := by
  have m₁ : Measurable fun x => a₁ x y := ha₁.comp (measurable_id.prodMk measurable_const)
  have m₂ : Measurable fun x => a₂ x y := ha₂.comp (measurable_id.prodMk measurable_const)
  exact (lintegral_prod_mul (f := fun x => a₁ x y) (g := fun x => a₂ x y) m₁.aemeasurable
    m₂.aemeasurable).symm

lemma core {a₁ : X₁ → Y → ℝ≥0∞} {a₂ : X₂ → Y → ℝ≥0∞} {b₁ : X₁ → ℝ≥0∞} {b₂ : X₂ → ℝ≥0∞}
    (ha₁ : Measurable (Function.uncurry a₁)) (ha₂ : Measurable (Function.uncurry a₂))
    (hb₁ : Measurable b₁) (hb₂ : Measurable b₂) {N₁ : X₁ → ℝ≥0∞} {N₂ : X₂ → ℝ≥0∞}
    (hN₁ : ∀ x, ∫⁻ y, a₁ x y ^ 2 ∂ν ≤ N₁ x ^ 2) (hN₂ : ∀ x, ∫⁻ y, a₂ x y ^ 2 ∂ν ≤ N₂ x ^ 2) :
    ∫⁻ y, (∫⁻ x₁, a₁ x₁ y * b₁ x₁ ∂μ₁) * (∫⁻ x₂, a₂ x₂ y * b₂ x₂ ∂μ₂) ∂ν ≤
      (∫⁻ x, N₁ x * b₁ x ∂μ₁) * (∫⁻ x, N₂ x * b₂ x ∂μ₂) := by
  have hA₁ : Measurable (Function.uncurry fun x y => a₁ x y * b₁ x) :=
    ha₁.mul (hb₁.comp measurable_fst)
  have hA₂ : Measurable (Function.uncurry fun x y => a₂ x y * b₂ x) :=
    ha₂.mul (hb₂.comp measurable_fst)

  set n₁ : X₁ → ℝ≥0∞ := fun x => (∫⁻ y, a₁ x y ^ (2:ℝ) ∂ν) ^ (1 / (2:ℝ)) with hn₁
  set n₂ : X₂ → ℝ≥0∞ := fun x => (∫⁻ y, a₂ x y ^ (2:ℝ) ∂ν) ^ (1 / (2:ℝ)) with hn₂
  have mn₁ : Measurable n₁ :=
    ((ha₁.pow_const (2:ℝ)).lintegral_prod_right' (ν := ν)).pow_const _
  have mn₂ : Measurable n₂ :=
    ((ha₂.pow_const (2:ℝ)).lintegral_prod_right' (ν := ν)).pow_const _
  have nN₁ : ∀ x, n₁ x ≤ N₁ x := fun x => sqrt_le_of_sq_le (by simpa [ENNReal.rpow_two] using hN₁ x)
  have nN₂ : ∀ x, n₂ x ≤ N₂ x := fun x => sqrt_le_of_sq_le (by simpa [ENNReal.rpow_two] using hN₂ x)
  have hsplit := lintegral_prod_split (μ₁ := μ₁) (μ₂ := μ₂) hA₁ hA₂
  simp only [hsplit]
  have hG : Measurable (Function.uncurry fun (y : Y) (p : X₁ × X₂) =>
      a₁ p.1 y * b₁ p.1 * (a₂ p.2 y * b₂ p.2)) := by
    have e₁ : Measurable fun z : Y × (X₁ × X₂) => a₁ z.2.1 z.1 * b₁ z.2.1 :=
      hA₁.comp ((measurable_fst.comp measurable_snd).prodMk measurable_fst)
    have e₂ : Measurable fun z : Y × (X₁ × X₂) => a₂ z.2.2 z.1 * b₂ z.2.2 :=
      hA₂.comp ((measurable_snd.comp measurable_snd).prodMk measurable_fst)
    exact e₁.mul e₂
  rw [lintegral_lintegral_swap hG.aemeasurable]
  calc ∫⁻ p : X₁ × X₂, ∫⁻ y, a₁ p.1 y * b₁ p.1 * (a₂ p.2 y * b₂ p.2) ∂ν ∂μ₁.prod μ₂
      ≤ ∫⁻ p : X₁ × X₂, (n₁ p.1 * b₁ p.1) * (n₂ p.2 * b₂ p.2) ∂μ₁.prod μ₂ := by
        refine lintegral_mono fun p => ?_
        have m₁ : Measurable fun y => a₁ p.1 y := ha₁.comp (measurable_const.prodMk measurable_id)
        have m₂ : Measurable fun y => a₂ p.2 y := ha₂.comp (measurable_const.prodMk measurable_id)
        calc ∫⁻ y, a₁ p.1 y * b₁ p.1 * (a₂ p.2 y * b₂ p.2) ∂ν
            = ∫⁻ y, (b₁ p.1 * b₂ p.2) * (a₁ p.1 y * a₂ p.2 y) ∂ν := by
              congr 1; funext y; ring
          _ = (b₁ p.1 * b₂ p.2) * ∫⁻ y, a₁ p.1 y * a₂ p.2 y ∂ν := lintegral_const_mul _ (m₁.mul m₂)
          _ ≤ (b₁ p.1 * b₂ p.2) * (n₁ p.1 * n₂ p.2) :=
              by gcongr; exact lintegral_mul_le_sqrt ν m₁ m₂
          _ = (n₁ p.1 * b₁ p.1) * (n₂ p.2 * b₂ p.2) := by ring
    _ = (∫⁻ x, n₁ x * b₁ x ∂μ₁) * (∫⁻ x, n₂ x * b₂ x ∂μ₂) :=
        lintegral_prod_mul (f := fun x => n₁ x * b₁ x) (g := fun x => n₂ x * b₂ x)
          (mn₁.mul hb₁).aemeasurable (mn₂.mul hb₂).aemeasurable
    _ ≤ (∫⁻ x, N₁ x * b₁ x ∂μ₁) * (∫⁻ x, N₂ x * b₂ x ∂μ₂) :=
        by
          gcongr with x x
          · exact nN₁ x
          · exact nN₂ x

lemma memLp_lift {k : X₁ → Y → ℂ} {u : X₁ → ℂ} (hk : Measurable (Function.uncurry k))
    (hu : Measurable u) {N : X₁ → ℝ≥0∞} (hN : ∀ x, ∫⁻ y, ‖k x y‖ₑ ^ 2 ∂ν ≤ N x ^ 2)
    (hfin : ∫⁻ x, N x * ‖u x‖ₑ ∂μ₁ ≠ ⊤) :
    MemLp (fun y => ∫ x, k x y * u x ∂μ₁) 2 ν := by
  have hF : Measurable fun q : Y × X₁ => k q.2 q.1 * u q.2 :=
    (hk.comp (measurable_snd.prodMk measurable_fst)).mul (hu.comp measurable_snd)
  have hsm : StronglyMeasurable fun y => ∫ x, k x y * u x ∂μ₁ :=
    hF.stronglyMeasurable.integral_prod_right'
  refine ⟨hsm.aestronglyMeasurable, ?_⟩
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)]
  refine ENNReal.rpow_lt_top_of_nonneg (by norm_num) ?_
  have hA : Measurable (Function.uncurry fun x y => ‖k x y‖ₑ) := hk.enorm
  have hb : Measurable fun x => ‖u x‖ₑ := hu.enorm
  have hc := core (μ₁ := μ₁) (μ₂ := μ₁) (ν := ν) hA hA hb hb hN hN
  refine ne_top_of_le_ne_top (ENNReal.mul_ne_top hfin hfin) (le_trans ?_ hc)
  refine lintegral_mono fun y => ?_
  have h1 : ‖∫ x, k x y * u x ∂μ₁‖ₑ ≤ ∫⁻ x, ‖k x y‖ₑ * ‖u x‖ₑ ∂μ₁ := by
    simpa only [enorm_mul] using enorm_integral_le_lintegral_enorm (μ := μ₁) (fun x => k x y * u x)
  simp only [ENNReal.toReal_ofNat, ENNReal.rpow_two, pow_two]
  exact mul_le_mul' h1 h1

theorem abstract_fubini_two_lifts : ∀ {X₁ X₂ Y : Type*} [MeasurableSpace X₁] [MeasurableSpace X₂] [MeasurableSpace Y]
    (μ₁ : Measure X₁) (μ₂ : Measure X₂) (ν : Measure Y) [SigmaFinite μ₁] [SigmaFinite μ₂] [SigmaFinite ν]
    (k₁ : X₁ → Y → ℂ) (k₂ : X₂ → Y → ℂ) (u₁ : X₁ → ℂ) (u₂ : X₂ → ℂ),
    Measurable (Function.uncurry k₁) → Measurable (Function.uncurry k₂) → Measurable u₁ → Measurable u₂ →
    ∀ (N₁ : X₁ → ENNReal) (N₂ : X₂ → ENNReal),
    (∀ x, ∫⁻ y, ‖k₁ x y‖ₑ ^ 2 ∂ν ≤ N₁ x ^ 2) → (∀ x, ∫⁻ y, ‖k₂ x y‖ₑ ^ 2 ∂ν ≤ N₂ x ^ 2) →
    ∫⁻ x, N₁ x * ‖u₁ x‖ₑ ∂μ₁ ≠ ⊤ → ∫⁻ x, N₂ x * ‖u₂ x‖ₑ ∂μ₂ ≠ ⊤ →
    (∀ y, Integrable (fun x => k₁ x y * u₁ x) μ₁) → (∀ y, Integrable (fun x => k₂ x y * u₂ x) μ₂) →
    MemLp (fun y => ∫ x, k₁ x y * u₁ x ∂μ₁) 2 ν ∧ MemLp (fun y => ∫ x, k₂ x y * u₂ x ∂μ₂) 2 ν ∧
    ∫ y, (∫ x, k₁ x y * u₁ x ∂μ₁) * conj (∫ x, k₂ x y * u₂ x ∂μ₂) ∂ν =
      ∫ p : X₁ × X₂, (∫ y, k₁ p.1 y * conj (k₂ p.2 y) ∂ν) * u₁ p.1 * conj (u₂ p.2) ∂μ₁.prod μ₂ := by
  intro X₁ X₂ Y _ _ _ μ₁ μ₂ ν _ _ _ k₁ k₂ u₁ u₂ hk₁ hk₂ hu₁ hu₂ N₁ N₂ hN₁ hN₂ hf₁ hf₂ _ _
  refine ⟨memLp_lift hk₁ hu₁ hN₁ hf₁, memLp_lift hk₂ hu₂ hN₂ hf₂, ?_⟩
  set F : Y → X₁ × X₂ → ℂ := fun y p => k₁ p.1 y * u₁ p.1 * conj (k₂ p.2 y * u₂ p.2) with hFdef
  have hFm : Measurable (Function.uncurry F) := by
    have e₁ : Measurable fun z : Y × (X₁ × X₂) => k₁ z.2.1 z.1 * u₁ z.2.1 :=
      (hk₁.comp ((measurable_fst.comp measurable_snd).prodMk measurable_fst)).mul
        (hu₁.comp (measurable_fst.comp measurable_snd))
    have e₂ : Measurable fun z : Y × (X₁ × X₂) => k₂ z.2.2 z.1 * u₂ z.2.2 :=
      (hk₂.comp ((measurable_snd.comp measurable_snd).prodMk measurable_fst)).mul
        (hu₂.comp (measurable_snd.comp measurable_snd))
    exact e₁.mul (Complex.continuous_conj.measurable.comp e₂)
  have hA₁ : Measurable (Function.uncurry fun x y => ‖k₁ x y‖ₑ) := hk₁.enorm
  have hA₂ : Measurable (Function.uncurry fun x y => ‖k₂ x y‖ₑ) := hk₂.enorm
  have hc := core (μ₁ := μ₁) (μ₂ := μ₂) (ν := ν) hA₁ hA₂ hu₁.enorm hu₂.enorm hN₁ hN₂
  have hFi : Integrable (Function.uncurry F) (ν.prod (μ₁.prod μ₂)) := by
    refine ⟨hFm.aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_enorm, lintegral_prod _ hFm.enorm.aemeasurable]
    refine lt_of_le_of_lt (le_of_eq ?_) (lt_of_le_of_lt hc
      (ENNReal.mul_lt_top hf₁.lt_top hf₂.lt_top))
    refine lintegral_congr fun y => ?_
    have hA₁' : Measurable (Function.uncurry fun x y => ‖k₁ x y‖ₑ * ‖u₁ x‖ₑ) :=
      hA₁.mul (hu₁.enorm.comp measurable_fst)
    have hA₂' : Measurable (Function.uncurry fun x y => ‖k₂ x y‖ₑ * ‖u₂ x‖ₑ) :=
      hA₂.mul (hu₂.enorm.comp measurable_fst)
    rw [lintegral_prod_split (μ₁ := μ₁) (μ₂ := μ₂) hA₁' hA₂' y]
    refine lintegral_congr fun p => ?_
    simp only [Function.uncurry_apply_pair, hFdef, enorm_mul, RCLike.enorm_conj]
  have hpt : ∀ y, (∫ x, k₁ x y * u₁ x ∂μ₁) * conj (∫ x, k₂ x y * u₂ x ∂μ₂) =
      ∫ p, F y p ∂μ₁.prod μ₂ := by
    intro y
    rw [← integral_conj]
    exact (integral_prod_mul (fun x => k₁ x y * u₁ x) (fun x => conj (k₂ x y * u₂ x))).symm
  simp_rw [hpt]
  rw [integral_integral_swap hFi]
  refine integral_congr_ae (Filter.Eventually.of_forall fun p => ?_)
  simp only [hFdef]
  have : ∀ y, k₁ p.1 y * u₁ p.1 * conj (k₂ p.2 y * u₂ p.2) =
      k₁ p.1 y * conj (k₂ p.2 y) * (u₁ p.1 * conj (u₂ p.2)) := by
    intro y; simp only [map_mul]; ring
  simp_rw [this]
  rw [integral_mul_const]
  ring

end GlobalTheory.AbsFubini
