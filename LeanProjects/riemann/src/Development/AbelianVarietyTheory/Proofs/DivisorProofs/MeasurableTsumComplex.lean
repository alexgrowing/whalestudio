import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.AnalyticOnNhdTsumNpow
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HolValueAtIntegralOfExpansion

open MeasureTheory

noncomputable section

namespace GlobalTheory.UnfoldPartial

open Filter Set GlobalTheory.Eis GlobalTheory.AutomorphicL2Unitary GlobalTheory.DefDoubling
open scoped ENNReal

theorem measurable_tsum_nonneg {X ι : Type} [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
    {p : ι → X → ℝ} (hc : ∀ i, Continuous (p i)) (h0 : ∀ i x, 0 ≤ p i x)
    (hs : ∀ x, Summable fun i => p i x) : Measurable fun x => ∑' i, p i x := by
  have hE : Measurable fun x => ∑' i, ENNReal.ofReal (p i x) :=
    (lowerSemicontinuous_tsum fun i => (ENNReal.continuous_ofReal.comp (hc i)).lowerSemicontinuous).measurable
  have e : (fun x => ∑' i, p i x) = fun x => (∑' i, ENNReal.ofReal (p i x)).toReal := funext fun x => by
    rw [← ENNReal.ofReal_tsum_of_nonneg (fun i => h0 i x) (hs x),
      ENNReal.toReal_ofReal (tsum_nonneg fun i => h0 i x)]
  rw [e]; exact hE.ennreal_toReal

theorem measurable_tsum_real {X ι : Type} [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
    {p : ι → X → ℝ} (hc : ∀ i, Continuous (p i)) (hs : ∀ x, Summable fun i => |p i x|) :
    Measurable fun x => ∑' i, p i x := by
  have s1 : ∀ x, Summable fun i => max (p i x) 0 := fun x =>
    (hs x).of_nonneg_of_le (fun i => le_max_right _ _) fun i => max_le (le_abs_self _) (abs_nonneg _)
  have s2 : ∀ x, Summable fun i => max (-p i x) 0 := fun x =>
    (hs x).of_nonneg_of_le (fun i => le_max_right _ _) fun i => max_le (neg_le_abs _) (abs_nonneg _)
  have e : (fun x => ∑' i, p i x) = fun x => ∑' i, max (p i x) 0 - ∑' i, max (-p i x) 0 := funext fun x => by
    rw [← (s1 x).tsum_sub (s2 x)]
    exact tsum_congr fun i => (max_zero_sub_max_neg_zero_eq_self _).symm
  rw [e]
  exact (measurable_tsum_nonneg (fun i => (hc i).max continuous_const) (fun i x => le_max_right _ _) s1).sub
    (measurable_tsum_nonneg (fun i => (hc i).neg.max continuous_const) (fun i x => le_max_right _ _) s2)

theorem measurable_tsum_complex {X ι : Type} [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
    {g : ι → X → ℂ} (hc : ∀ i, Continuous (g i)) (hs : ∀ x, Summable fun i => ‖g i x‖) :
    Measurable fun x => ∑' i, g i x := by
  have sr : ∀ x, Summable fun i => |(g i x).re| := fun x =>
    (hs x).of_nonneg_of_le (fun i => abs_nonneg _) fun i => Complex.abs_re_le_norm _
  have si : ∀ x, Summable fun i => |(g i x).im| := fun x =>
    (hs x).of_nonneg_of_le (fun i => abs_nonneg _) fun i => Complex.abs_im_le_norm _
  have e : (fun x => ∑' i, g i x) =
      fun x => ((∑' i, (g i x).re : ℝ) : ℂ) + ((∑' i, (g i x).im : ℝ) : ℂ) * Complex.I := funext fun x => by
    apply Complex.ext <;> simp [Complex.re_tsum (hs x).of_norm, Complex.im_tsum (hs x).of_norm]
  rw [e]
  exact (Complex.measurable_ofReal.comp (measurable_tsum_real (fun i => Complex.continuous_re.comp (hc i)) sr)).add
    ((Complex.measurable_ofReal.comp (measurable_tsum_real (fun i => Complex.continuous_im.comp (hc i)) si)).mul_const _)

theorem unfold_of_nonopen_zero {G G₂ : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G]
    [BorelSpace G] [Group G₂] [TopologicalSpace G₂] [IsTopologicalGroup G₂] (i : G × G →* G₂) (P Γ₂ : Subgroup G₂)
    (Γ : Subgroup G) [Countable Γ] (μ : Measure G) [μ.IsMulLeftInvariant] (𝓕 : Set G) (Φ : G₂ → ℂ) (f w c : G → ℂ)
    (hi : Continuous i) (h𝓕 : IsFundamentalDomain Γ 𝓕 μ) (hΦ : LeftInv (P ⊓ Γ₂) Φ) (hΦc : Continuous Φ)
    (hΓ : ∀ δ ∈ Γ, i (1, δ) ∈ Γ₂) (hP : ∀ δ δ' : G, i (1, δ) * (i (1, δ'))⁻¹ ∈ P → δ = δ')
    (hconv : ∀ g, CosetConv P Γ₂ Φ g) (hf : Continuous f) (hfΓ : ∀ γ ∈ Γ, ∀ x, f (γ * x) = f x)
    (hwc : Continuous w) (hw : ∀ x y, w (x * y) = w x * w y) (hwΓ : ∀ γ ∈ Γ, w γ = 1) (hw1 : ∀ x, ‖w x‖ = 1)
    (hlaw : ∀ h y, Φ (i (h, h) * y) = c h * Φ y) (hcw : ∀ h, c h * w h = 1) (h : G)
    (hfin : ∫⁻ x in 𝓕, ‖f x‖ₑ * ∑' q, ‖term P Γ₂ Φ (i (h, x)) q‖ₑ ∂μ ≠ ⊤)
    (hnon : ∫ x in 𝓕, f x * (∑' q : {q : Cosets P Γ₂ // ¬ ∃ δ ∈ Γ, ((q.out : Γ₂) : G₂) * (i (1, δ))⁻¹ ∈ P},
      term P Γ₂ Φ (i (h, x)) q.1) * w x ∂μ = 0) :
    ∫ x in 𝓕, f x * (cosetSum P Γ₂ Φ (i (h, x)) * w x) ∂μ = ∫ g, Φ (i (1, g)) * w g * f (h * g) ∂μ := by
  classical
  set O : Set (Cosets P Γ₂) := {q | ∃ δ ∈ Γ, ((q.out : Γ₂) : G₂) * (i (1, δ))⁻¹ ∈ P} with hO
  let r : Γ → Γ₂ := fun δ => ⟨i (1, δ), hΓ δ δ.2⟩
  have hmem : ∀ δ : Γ, mk (P.subgroupOf Γ₂) (r δ) ∈ O := fun δ => by
    obtain ⟨γ, hγ⟩ := mk_eq_iff.1 (Quotient.out_eq (mk (P.subgroupOf Γ₂) (r δ)))
    have h2 : ((γ : Γ₂) : G₂) * (((mk (P.subgroupOf Γ₂) (r δ)).out : Γ₂) : G₂) = i (1, δ) :=
      congrArg Subtype.val hγ
    refine ⟨δ, δ.2, ?_⟩
    rw [← h2, mul_inv_rev, mul_inv_cancel_left]
    exact P.inv_mem (Subgroup.mem_subgroupOf.1 γ.2)
  let e : Γ → O := fun δ => ⟨mk (P.subgroupOf Γ₂) (r δ), hmem δ⟩
  have he : Function.Bijective e := by
    constructor
    · intro δ δ' hδ
      have h1 : mk (P.subgroupOf Γ₂) (r δ) = mk (P.subgroupOf Γ₂) (r δ') := congrArg Subtype.val hδ
      obtain ⟨γ, hγ⟩ := mk_eq_iff.1 h1
      have h2 : ((γ : Γ₂) : G₂) * i (1, δ) = i (1, δ') := congrArg Subtype.val hγ
      apply Subtype.ext
      apply hP
      rw [← h2, mul_inv_rev, mul_inv_cancel_left]
      exact P.inv_mem (Subgroup.mem_subgroupOf.1 γ.2)
    · rintro ⟨q, δ, hδ, hq⟩
      refine ⟨⟨δ, hδ⟩, Subtype.ext ?_⟩
      exact (mk_eq_iff.2 ⟨⟨q.out * (r ⟨δ, hδ⟩)⁻¹, Subgroup.mem_subgroupOf.2 hq⟩, inv_mul_cancel_right _ _⟩).trans
        (Quotient.out_eq q)
  have hterm : ∀ x (δ : Γ), term P Γ₂ Φ (i (h, x)) (e δ).1 = Φ (i (h, δ * x)) := fun x δ => by
    show term P Γ₂ Φ (i (h, x)) (mk _ (r δ)) = _
    rw [term_mk hΦ]
    show Φ (i (1, δ) * i (h, x)) = _
    rw [← map_mul, Prod.mk_mul_mk, one_mul]
  have hopen : ∀ x, ∑' q : O, term P Γ₂ Φ (i (h, x)) q = ∑' δ : Γ, Φ (i (h, δ * x)) := fun x => by
    rw [← (Equiv.ofBijective e he).tsum_eq]
    exact tsum_congr fun δ => hterm x δ
  have hsplit : ∀ x, cosetSum P Γ₂ Φ (i (h, x)) = ∑' δ : Γ, Φ (i (h, δ * x)) +
      ∑' q : {q : Cosets P Γ₂ // ¬ ∃ δ ∈ Γ, ((q.out : Γ₂) : G₂) * (i (1, δ))⁻¹ ∈ P},
        term P Γ₂ Φ (i (h, x)) q.1 := fun x => by
    rw [← hopen x]; exact ((hconv _).of_norm.tsum_subtype_add_tsum_subtype_compl O).symm
  set F : G → ℂ := fun x => f x * Φ (i (h, x)) * w x with hF
  have hic : ∀ y : G, Continuous fun x : G => i (y, x) := fun y => hi.comp (continuous_const.prodMk continuous_id)
  have hFc : Continuous F := (hf.mul (hΦc.comp (hic h))).mul hwc
  have hw1e : ∀ x, ‖w x‖ₑ = 1 := fun x => by rw [← ofReal_norm_eq_enorm, hw1, ENNReal.ofReal_one]
  have hFδ : ∀ x (δ : Γ), F (δ * x) = f x * Φ (i (h, δ * x)) * w x := fun x δ => by
    simp only [hF, hfΓ _ δ.2, hw, hwΓ _ δ.2, one_mul]
  have hFi : Integrable F μ := by
    refine ⟨hFc.aestronglyMeasurable, ?_⟩
    show ∫⁻ x, ‖F x‖ₑ ∂μ < ⊤
    rw [← lintegral_tsum_eq h𝓕 hFc.measurable.enorm.aemeasurable]
    refine lt_of_le_of_lt (lintegral_mono fun x => ?_) (lt_top_iff_ne_top.2 hfin)
    simp only [hFδ, enorm_mul, hw1e, mul_one]
    rw [ENNReal.tsum_mul_left]
    refine mul_le_mul' le_rfl ?_
    calc ∑' δ : Γ, ‖Φ (i (h, δ * x))‖ₑ = ∑' δ : Γ, ‖term P Γ₂ Φ (i (h, x)) (e δ).1‖ₑ :=
          tsum_congr fun δ => by rw [hterm]
      _ ≤ _ := ENNReal.tsum_comp_le_tsum_of_injective (Subtype.val_injective.comp he.1) _
  have hopenF : ∀ x, ∑' δ : Γ, F (δ * x) = f x * (∑' δ : Γ, Φ (i (h, δ * x))) * w x := fun x => by
    rw [tsum_congr (hFδ x), tsum_mul_right, tsum_mul_left]
  set C : G → ℂ := fun x => f x * (∑' q : {q : Cosets P Γ₂ // ¬ ∃ δ ∈ Γ, ((q.out : Γ₂) : G₂) * (i (1, δ))⁻¹ ∈ P},
      term P Γ₂ Φ (i (h, x)) q.1) * w x with hC
  have hNm : Measurable fun x => ∑' q : {q : Cosets P Γ₂ // ¬ ∃ δ ∈ Γ, ((q.out : Γ₂) : G₂) * (i (1, δ))⁻¹ ∈ P},
      term P Γ₂ Φ (i (h, x)) q.1 :=
    measurable_tsum_complex (fun q => hΦc.comp (continuous_const.mul (hic h)))
      fun x => (hconv (i (h, x))).subtype Oᶜ
  have hCi : IntegrableOn C 𝓕 μ := by
    refine ⟨((hf.measurable.mul hNm).mul hwc.measurable).aestronglyMeasurable, ?_⟩
    refine lt_of_le_of_lt (lintegral_mono fun x => ?_) (lt_top_iff_ne_top.2 hfin)
    rw [hC]
    simp only [enorm_mul, hw1e, mul_one]
    exact mul_le_mul' le_rfl (enorm_tsum_le_tsum_enorm.trans
      (ENNReal.tsum_comp_le_tsum_of_injective Subtype.val_injective _))
  obtain ⟨h1, h2⟩ := integral_tsum_eq h𝓕 hFi
  have hA : ∀ x, f x * (cosetSum P Γ₂ Φ (i (h, x)) * w x) = ∑' δ : Γ, F (δ * x) + C x := fun x => by
    rw [hsplit x, hopenF x, hC]; ring
  simp_rw [hA]
  rw [integral_add h1 hCi, h2, hnon, add_zero, ← integral_mul_left_eq_self F h]
  refine integral_congr_ae (Eventually.of_forall fun g => ?_)
  have : i (h, h * g) = i (h, h) * i (1, g) := by rw [← map_mul, Prod.mk_mul_mk, mul_one]
  simp only [hF, this, hlaw, hw]
  linear_combination (f (h * g) * Φ (i (1, g)) * w g) * hcw h

end GlobalTheory.UnfoldPartial
