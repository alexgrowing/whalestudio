import Mathlib

open MeasureTheory Set Function
open scoped ENNReal

namespace GroundTheory.Automorphic.GJGlobal

noncomputable section

namespace Unfold

theorem tsum_eq_tsum_quotient {α : Type*} [Group α] (s : Subgroup α) (f : α → ℝ≥0∞) :
    ∑' a, f a = ∑' c : α ⧸ s, ∑' b : s, f (c.out * b) := by
  have hbij : Bijective (fun x : (α ⧸ s) × s => x.1.out * (x.2 : α)) := by
    constructor
    · rintro ⟨c, b⟩ ⟨c', b'⟩ hx
      simp only at hx
      have hc : c = c' := by
        have h1 : (QuotientGroup.mk (c.out * (b : α)) : α ⧸ s) = c := by
          rw [QuotientGroup.mk_mul_of_mem _ b.2, QuotientGroup.out_eq']
        have h2 : (QuotientGroup.mk (c'.out * (b' : α)) : α ⧸ s) = c' := by
          rw [QuotientGroup.mk_mul_of_mem _ b'.2, QuotientGroup.out_eq']
        rw [← h1, ← h2, hx]
      subst hc
      exact Prod.ext rfl (Subtype.ext (mul_left_cancel hx))
    · intro a
      refine ⟨(QuotientGroup.mk a, ⟨(QuotientGroup.mk a : α ⧸ s).out⁻¹ * a, ?_⟩), ?_⟩
      · rw [← QuotientGroup.eq, QuotientGroup.out_eq']
      · simp
  rw [← (Equiv.ofBijective _ hbij).tsum_eq]
  exact ENNReal.tsum_prod (f := fun (c : α ⧸ s) (b : s) => f (c.out * b))

variable {G : Type*} [Group G] [MeasurableSpace G]
  {V : Type*} [AddCommGroup V] [MeasurableSpace V]

structure Hyp (ν : Measure V) (u : V → G) (L : AddSubgroup V) (D : Set V) (Λ : Subgroup G)
    (E : Set G) (S : G → V →+ V) : Prop where
  map_add : ∀ X Y, u (X + Y) = u X * u Y
  injective : Injective u
  measurable : Measurable u
  isAddFundamentalDomain : IsAddFundamentalDomain L D ν
  measurableSet_D : MeasurableSet D
  measurableSet_E : MeasurableSet E
  existsUnique : ∀ g : G, ∃! p : Λ, (p : G) * g ∈ E
  mem : ∀ ξ ∈ L, u ξ ∈ Λ
  conj : ∀ q ∈ Λ, ∀ Z, q⁻¹ * u Z * q = u (S q Z)
  mapsTo : ∀ q ∈ Λ, ∀ ξ ∈ L, S q ξ ∈ L
  measurePreserving : ∀ q ∈ Λ, MeasurePreserving (S q) ν ν

namespace Hyp

variable {ν : Measure V} {u : V → G} {L : AddSubgroup V} {D : Set V} {Λ : Subgroup G} {E : Set G}
  {S : G → V →+ V}

theorem map_zero (h : Hyp ν u L D Λ E S) : u 0 = 1 := by
  have h0 := h.map_add 0 0
  rw [add_zero] at h0
  exact mul_eq_left.1 h0.symm

theorem map_neg (h : Hyp ν u L D Λ E S) (X : V) : u (-X) = (u X)⁻¹ :=
  eq_inv_of_mul_eq_one_left (by rw [← h.map_add, neg_add_cancel, h.map_zero])

theorem S_S_inv (h : Hyp ν u L D Λ E S) {q : G} (hq : q ∈ Λ) (Z : V) : S q (S q⁻¹ Z) = Z := by
  apply h.injective
  rw [← h.conj q hq, ← h.conj q⁻¹ (inv_mem hq)]
  simp [mul_assoc]

def unipSubgroup (h : Hyp ν u L D Λ E S) : Subgroup Λ where
  carrier := {p | ∃ ξ ∈ L, u ξ = p}
  one_mem' := ⟨0, L.zero_mem, h.map_zero⟩
  mul_mem' := by
    rintro _ _ ⟨ξ, hξ, hξe⟩ ⟨η, hη, hηe⟩
    exact ⟨ξ + η, L.add_mem hξ hη, by rw [h.map_add, hξe, hηe]; rfl⟩
  inv_mem' := by
    rintro _ ⟨ξ, hξ, hξe⟩
    exact ⟨-ξ, L.neg_mem hξ, by rw [h.map_neg, hξe]; rfl⟩

def unipEquiv (h : Hyp ν u L D Λ E S) : L ≃ h.unipSubgroup :=
  Equiv.ofBijective (fun ξ => ⟨⟨u ξ, h.mem ξ ξ.2⟩, ⟨ξ, ξ.2, rfl⟩⟩)
    ⟨fun _ _ hξη => Subtype.ext (h.injective (congrArg (fun x : h.unipSubgroup => ((x : Λ) : G)) hξη)),
      fun ⟨_, ξ, hξ, hξe⟩ => ⟨⟨ξ, hξ⟩, Subtype.ext (Subtype.ext hξe)⟩⟩

theorem coe_unipEquiv (h : Hyp ν u L D Λ E S) (ξ : L) : (((h.unipEquiv ξ : h.unipSubgroup) : Λ) : G) = u ξ :=
  rfl

def latticeEquiv (h : Hyp ν u L D Λ E S) {q : G} (hq : q ∈ Λ) : L ≃ L where
  toFun η := ⟨S q (-η), h.mapsTo q hq _ (L.neg_mem η.2)⟩
  invFun ξ := ⟨-S q⁻¹ ξ, L.neg_mem (h.mapsTo q⁻¹ (inv_mem hq) _ ξ.2)⟩
  left_inv η := by
    refine Subtype.ext ?_
    have := h.S_S_inv (inv_mem hq) (-(η : V))
    rw [inv_inv] at this
    show -S q⁻¹ (S q (-(η : V))) = η
    rw [this, neg_neg]
  right_inv ξ := by
    refine Subtype.ext ?_
    simp [h.S_S_inv hq]

end Hyp

section Counting

set_option linter.unusedSectionVars false

variable [MeasurableMul G] [MeasurableAdd V] [MeasurableNeg V]
  {ν : Measure V} [ν.IsAddLeftInvariant] [ν.IsNegInvariant] [SFinite ν]
  {u : V → G} {L : AddSubgroup V} {D : Set V} {Λ : Subgroup G} {E : Set G} {S : G → V →+ V}
  [Countable Λ] [Countable L]

namespace Hyp

theorem measurable_indicator (h : Hyp ν u L D Λ E S) (q g : G) :
    Measurable (fun Z : V => E.indicator (1 : G → ℝ≥0∞) (q * u Z * g)) :=
  (measurable_one.indicator h.measurableSet_E).comp ((h.measurable.const_mul q).mul_const g)

theorem tsum_setLIntegral_right (h : Hyp ν u L D Λ E S) (q g : G) :
    ∑' ξ : L, ∫⁻ Y in D, E.indicator 1 (q * u ξ * u Y * g) ∂ν =
      ∫⁻ Z, E.indicator 1 (q * u Z * g) ∂ν := by
  rw [h.isAddFundamentalDomain.lintegral_eq_tsum'' (fun Z => E.indicator 1 (q * u Z * g))]
  refine tsum_congr fun ξ => setLIntegral_congr_fun h.measurableSet_D (fun Y _ => ?_)
  rw [AddSubgroup.vadd_def, vadd_eq_add, h.map_add, ← mul_assoc]

theorem tsum_setLIntegral_left (h : Hyp ν u L D Λ E S) {q : G} (hq : q ∈ Λ) (g : G) :
    ∑' ξ : L, ∫⁻ X in D, E.indicator 1 (u (-X) * (q * u ξ) * g) ∂ν =
      ∫⁻ Z, E.indicator 1 (q * u Z * g) ∂ν := by
  have key : ∀ (X : V) (η : L), u (-X) * (q * u ((h.latticeEquiv hq η : L) : V)) * g =
      q * u (S q (-((η : V) + X))) * g := by
    intro X η
    have e1 : ((h.latticeEquiv hq η : L) : V) = S q (-(η : V)) := rfl
    have e2 : S q (-((η : V) + X)) = S q (-X) + S q (-(η : V)) := by
      rw [neg_add, (S q).map_add, add_comm]
    rw [e1, e2, h.map_add, ← h.conj q hq (-X)]
    simp only [mul_assoc, mul_inv_cancel_left]
  rw [← (h.latticeEquiv hq).tsum_eq]
  simp_rw [key]
  have hmp : MeasurePreserving (fun W : V => S q (-W)) ν ν :=
    (h.measurePreserving q hq).comp (Measure.measurePreserving_neg ν)
  rw [← hmp.lintegral_comp (h.measurable_indicator q g),
    h.isAddFundamentalDomain.lintegral_eq_tsum'' (fun W => E.indicator 1 (q * u (S q (-W)) * g))]
  refine tsum_congr fun η => setLIntegral_congr_fun h.measurableSet_D (fun X _ => ?_)
  rw [AddSubgroup.vadd_def, vadd_eq_add]

theorem tsum_setLIntegral_indicator (h : Hyp ν u L D Λ E S) (g : G) :
    ∑' p : Λ, ∫⁻ X in D, E.indicator 1 (u (-X) * p * g) ∂ν = ν D := by
  have hb : ∑' p : Λ, ∫⁻ Y in D, E.indicator 1 ((p : G) * u Y * g) ∂ν = ν D := by
    rw [← lintegral_tsum fun p : Λ => (h.measurable_indicator (p : G) g).aemeasurable]
    have hone : ∀ Y, ∑' p : Λ, E.indicator (1 : G → ℝ≥0∞) ((p : G) * u Y * g) = 1 := by
      intro Y
      obtain ⟨p, hp, hpu⟩ := h.existsUnique (u Y * g)
      rw [tsum_eq_single p]
      · rw [mul_assoc, indicator_of_mem hp]
        rfl
      · intro p' hp'
        rw [mul_assoc, indicator_of_notMem]
        exact fun hm => hp' (hpu p' hm)
    simp_rw [hone]
    simp
  rw [← hb, tsum_eq_tsum_quotient h.unipSubgroup,
    tsum_eq_tsum_quotient h.unipSubgroup (fun p : Λ => ∫⁻ Y in D, E.indicator 1 ((p : G) * u Y * g) ∂ν)]
  refine tsum_congr fun c => ?_
  rw [← h.unipEquiv.tsum_eq, ← h.unipEquiv.tsum_eq]
  simp only [Subgroup.coe_mul, coe_unipEquiv]
  rw [h.tsum_setLIntegral_left c.out.2 g, h.tsum_setLIntegral_right]

end Hyp

end Counting

section Integral

set_option linter.unusedSectionVars false

variable [MeasurableMul G] [MeasurableMul₂ G] [MeasurableAdd V] [MeasurableNeg V]
  {ν : Measure V} [ν.IsAddLeftInvariant] [ν.IsNegInvariant] [SFinite ν]
  {μ : Measure G} [μ.IsMulLeftInvariant] [SFinite μ]
  {u : V → G} {L : AddSubgroup V} {D : Set V} {Λ : Subgroup G} {E : Set G} {S : G → V →+ V}
  [Countable Λ] [Countable L]

namespace Hyp

theorem isFundamentalDomain (h : Hyp ν u L D Λ E S) : IsFundamentalDomain Λ E μ :=
  IsFundamentalDomain.mk' h.measurableSet_E.nullMeasurableSet h.existsUnique

theorem measurable_indicator_prod (h : Hyp ν u L D Λ E S) :
    Measurable (fun p : V × G => E.indicator (1 : G → ℝ≥0∞) (u (-p.1) * p.2)) :=
  (measurable_one.indicator h.measurableSet_E).comp
    (((h.measurable.comp measurable_neg).comp measurable_fst).mul measurable_snd)

def weight (ν : Measure V) (u : V → G) (D : Set V) (E : Set G) (g : G) : ℝ≥0∞ :=
  ∫⁻ X in D, E.indicator 1 (u (-X) * g) ∂ν

theorem measurable_weight (h : Hyp ν u L D Λ E S) : Measurable (weight ν u D E) :=
  (h.measurable_indicator_prod).lintegral_prod_left'

theorem tsum_weight (h : Hyp ν u L D Λ E S) (g : G) : ∑' p : Λ, weight ν u D E (p * g) = ν D := by
  rw [← h.tsum_setLIntegral_indicator g]
  refine tsum_congr fun p => ?_
  simp only [weight, mul_assoc]

omit [MeasurableMul G] [MeasurableMul₂ G] [MeasurableAdd V] [MeasurableNeg V] [ν.IsAddLeftInvariant]
  [ν.IsNegInvariant] [SFinite ν] [Countable Λ] [Countable L] in
theorem weight_le (g : G) : weight ν u D E g ≤ ν D := by
  calc weight ν u D E g ≤ ∫⁻ _ in D, 1 ∂ν :=
        lintegral_mono fun X => indicator_le_self' (fun _ _ => zero_le_one) _
    _ = ν D := by simp

theorem setLIntegral_comp_mul (h : Hyp ν u L D Λ E S) (X : V) (H : G → ℝ≥0∞) :
    ∫⁻ g in E, H (u X * g) ∂μ = ∫⁻ g, E.indicator 1 (u (-X) * g) * H g ∂μ := by
  rw [← lintegral_indicator h.measurableSet_E,
    ← lintegral_mul_left_eq_self (fun g => E.indicator 1 (u (-X) * g) * H g) (u X)]
  refine lintegral_congr fun g => ?_
  simp only [← mul_assoc]
  rw [← h.map_add, neg_add_cancel, h.map_zero, one_mul]
  by_cases hg : g ∈ E <;> simp [hg]

theorem lintegral_weight_mul (h : Hyp ν u L D Λ E S) {H : G → ℝ≥0∞} (hH : Measurable H)
    (hΛ : ∀ p ∈ Λ, ∀ g, H (p * g) = H g) :
    ∫⁻ g, weight ν u D E g * H g ∂μ = ν D * ∫⁻ g in E, H g ∂μ := by
  rw [(h.isFundamentalDomain (μ := μ)).lintegral_eq_tsum'', ← lintegral_tsum]
  · rw [← lintegral_const_mul _ hH]
    refine setLIntegral_congr_fun h.measurableSet_E (fun g _ => ?_)
    simp only [Subgroup.smul_def, smul_eq_mul]
    have : ∀ p : Λ, weight ν u D E (p * g) * H (p * g) = weight ν u D E (p * g) * H g :=
      fun p => by rw [hΛ p p.2 g]
    simp_rw [this]
    rw [ENNReal.tsum_mul_right, h.tsum_weight]
  · intro p
    exact ((h.measurable_weight.mul hH).comp (measurable_const_mul (p : G))).aemeasurable.restrict

theorem lintegral_indicator_mul (h : Hyp ν u L D Λ E S) {H : G → ℝ≥0∞} (hH : Measurable H) :
    ∫⁻ X in D, ∫⁻ g, E.indicator 1 (u (-X) * g) * H g ∂μ ∂ν = ∫⁻ g, weight ν u D E g * H g ∂μ := by
  rw [lintegral_lintegral_swap ((h.measurable_indicator_prod.mul (hH.comp measurable_snd)).aemeasurable)]
  refine lintegral_congr fun g => ?_
  have hm : Measurable (fun X : V => E.indicator (1 : G → ℝ≥0∞) (u (-X) * g)) :=
    h.measurable_indicator_prod.comp (measurable_id.prodMk measurable_const)
  rw [lintegral_mul_const _ hm]
  rfl

theorem lintegral_setLIntegral_eq (h : Hyp ν u L D Λ E S) {H : G → ℝ≥0∞} (hH : Measurable H)
    (hΛ : ∀ p ∈ Λ, ∀ g, H (p * g) = H g) :
    ∫⁻ X in D, ∫⁻ g in E, H (u X * g) ∂μ ∂ν = ν D * ∫⁻ g in E, H g ∂μ := by
  simp_rw [h.setLIntegral_comp_mul]
  rw [h.lintegral_indicator_mul hH, h.lintegral_weight_mul hH hΛ]

theorem enorm_indicator_real (x : G) :
    ‖((E.indicator (1 : G → ℝ) x : ℝ) : ℂ)‖ₑ = E.indicator (1 : G → ℝ≥0∞) x := by
  by_cases hx : x ∈ E <;> simp [hx]

omit [MeasurableMul G] [MeasurableMul₂ G] [MeasurableAdd V] [MeasurableNeg V] [ν.IsAddLeftInvariant]
  [ν.IsNegInvariant] [SFinite ν] [Countable Λ] [Countable L] [μ.IsMulLeftInvariant] [SFinite μ] in
theorem enorm_toReal_coe {w : ℝ≥0∞} (hw : w ≠ ∞) : ‖((w.toReal : ℝ) : ℂ)‖ₑ = w := by
  rw [← ofReal_norm, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ENNReal.toReal_nonneg,
    ENNReal.ofReal_toReal hw]

theorem integral_indicator_real (h : Hyp ν u L D Λ E S) (g : G) :
    ∫ X in D, E.indicator (1 : G → ℝ) (u (-X) * g) ∂ν = (weight ν u D E g).toReal := by
  have hm : Measurable (fun X : V => E.indicator (1 : G → ℝ) (u (-X) * g)) :=
    (measurable_one.indicator h.measurableSet_E).comp
      ((h.measurable.comp measurable_neg).mul_const g)
  refine (integral_eq_lintegral_of_nonneg_ae (f := fun X => E.indicator (1 : G → ℝ) (u (-X) * g))
    (Filter.Eventually.of_forall fun X => indicator_nonneg (fun _ _ => zero_le_one) _)
    hm.aestronglyMeasurable).trans ?_
  congr 1
  refine lintegral_congr fun X => ?_
  by_cases hX : u (-X) * g ∈ E <;> simp [hX]

theorem integral_setIntegral_eq (h : Hyp ν u L D Λ E S) {Ψ : G → ℂ} (hΨ : Measurable Ψ)
    (hΛ : ∀ p ∈ Λ, ∀ g, Ψ (p * g) = Ψ g) (hint : ∫⁻ g in E, ‖Ψ g‖ₑ ∂μ < ∞) (hDtop : ν D ≠ ∞) :
    ∫ X in D, ∫ g in E, Ψ (u X * g) ∂μ ∂ν = (ν D).toReal * ∫ g in E, Ψ g ∂μ := by
  set ind : V → G → ℂ := fun X g => ((E.indicator (1 : G → ℝ) (u (-X) * g) : ℝ) : ℂ) with hind
  have hmind : Measurable (uncurry ind) := by
    refine Complex.measurable_ofReal.comp ?_
    exact (measurable_one.indicator h.measurableSet_E).comp
      (((h.measurable.comp measurable_neg).comp measurable_fst).mul measurable_snd)
  have hHm : Measurable fun g => ‖Ψ g‖ₑ := hΨ.enorm
  have hHΛ : ∀ p ∈ Λ, ∀ g, ‖Ψ (p * g)‖ₑ = ‖Ψ g‖ₑ := fun p hp g => by rw [hΛ p hp g]

  have hfin : ∫⁻ g, weight ν u D E g * ‖Ψ g‖ₑ ∂μ < ∞ := by
    rw [h.lintegral_weight_mul hHm hHΛ]
    exact ENNReal.mul_lt_top hDtop.lt_top hint

  have ha : ∀ X, ∫ g in E, Ψ (u X * g) ∂μ = ∫ g, ind X g * Ψ g ∂μ := by
    intro X
    rw [← integral_indicator h.measurableSet_E,
      ← integral_mul_left_eq_self (fun g => ind X g * Ψ g) (u X)]
    refine integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
    simp only [hind, ← mul_assoc]
    rw [← h.map_add, neg_add_cancel, h.map_zero, one_mul]
    by_cases hg : g ∈ E <;> simp [hg]
  simp_rw [ha]

  have hm0 : Measurable (uncurry fun X g => ind X g * Ψ g) := hmind.mul (hΨ.comp measurable_snd)
  have hI : Integrable (uncurry fun X g => ind X g * Ψ g) ((ν.restrict D).prod μ) := by
    refine ⟨hm0.aestronglyMeasurable, ?_⟩
    rw [HasFiniteIntegral, lintegral_prod _ hm0.enorm.aemeasurable]
    simp only [uncurry_apply_pair, enorm_mul, hind, enorm_indicator_real]
    rw [h.lintegral_indicator_mul hHm]
    exact hfin
  rw [integral_integral_swap hI]

  have hc : ∀ g, ∫ X in D, ind X g * Ψ g ∂ν = ((weight ν u D E g).toReal : ℂ) * Ψ g := by
    intro g
    rw [integral_mul_const, hind]
    simp only
    rw [integral_complex_ofReal, h.integral_indicator_real]
  simp_rw [hc]

  have hwm : Measurable fun g => ((weight ν u D E g).toReal : ℂ) * Ψ g :=
    (Complex.measurable_ofReal.comp h.measurable_weight.ennreal_toReal).mul hΨ
  have hen : ∀ g, ‖((weight ν u D E g).toReal : ℂ) * Ψ g‖ₑ = weight ν u D E g * ‖Ψ g‖ₑ := by
    intro g
    rw [enorm_mul, enorm_toReal_coe (ne_top_of_le_ne_top hDtop (weight_le g))]
  have hInt : Integrable (fun g => ((weight ν u D E g).toReal : ℂ) * Ψ g) μ := by
    refine ⟨hwm.aestronglyMeasurable, ?_⟩
    rw [HasFiniteIntegral]
    simp_rw [hen]
    exact hfin
  rw [(h.isFundamentalDomain (μ := μ)).integral_eq_tsum'' _ hInt]
  simp only [Subgroup.smul_def, smul_eq_mul]
  have hinv : ∀ (p : Λ) g, ((weight ν u D E (p * g)).toReal : ℂ) * Ψ (p * g) =
      ((weight ν u D E (p * g)).toReal : ℂ) * Ψ g := fun p g => by rw [hΛ p p.2 g]
  simp_rw [hinv]
  rw [← integral_tsum, ← integral_const_mul]
  · refine setIntegral_congr_fun h.measurableSet_E (fun g _ => ?_)
    rw [tsum_mul_right, ← Complex.ofReal_tsum, ← ENNReal.tsum_toReal_eq
      (fun p => ne_top_of_le_ne_top hDtop (weight_le _)), h.tsum_weight]
  · intro p
    exact ((Complex.measurable_ofReal.comp
      (h.measurable_weight.comp (measurable_const_mul (p : G))).ennreal_toReal).mul
        hΨ).aestronglyMeasurable.restrict
  · have : ∀ p : Λ, ∫⁻ g in E, ‖((weight ν u D E (p * g)).toReal : ℂ) * Ψ g‖ₑ ∂μ =
        ∫⁻ g in E, weight ν u D E (p * g) * ‖Ψ g‖ₑ ∂μ := by
      intro p
      refine lintegral_congr fun g => ?_
      rw [enorm_mul, enorm_toReal_coe (ne_top_of_le_ne_top hDtop (weight_le _))]
    simp_rw [this]
    rw [← lintegral_tsum]
    · simp_rw [ENNReal.tsum_mul_right, h.tsum_weight]
      rw [lintegral_const_mul _ hHm]
      exact (ENNReal.mul_lt_top hDtop.lt_top hint).ne
    · intro p
      exact ((h.measurable_weight.comp (measurable_const_mul (p : G))).mul hHm).aemeasurable.restrict

theorem setIntegral_mul_eq_zero (h : Hyp ν u L D Λ E S) {ψ F : G → ℂ} (hψ : Measurable ψ)
    (hF : Measurable F) (hΛ : ∀ p ∈ Λ, ∀ g, ψ (p * g) * F (p * g) = ψ g * F g)
    (hFu : ∀ X g, F (u X * g) = F g) (hint : ∫⁻ g in E, ‖ψ g * F g‖ₑ ∂μ < ∞)
    (hct : ∀ g, ∫ X in D, ψ (u X * g) ∂ν = 0) (hD0 : ν D ≠ 0) (hDtop : ν D ≠ ∞) :
    ∫ g in E, ψ g * F g ∂μ = 0 := by
  have key := h.integral_setIntegral_eq (μ := μ) (Ψ := fun g => ψ g * F g) (hψ.mul hF) hΛ hint hDtop
  have hm : Measurable (uncurry fun (X : V) (g : G) => ψ (u X * g) * F g) :=
    (hψ.comp ((h.measurable.comp measurable_fst).mul measurable_snd)).mul (hF.comp measurable_snd)
  have hI : Integrable (uncurry fun (X : V) (g : G) => ψ (u X * g) * F g)
      ((ν.restrict D).prod (μ.restrict E)) := by
    refine ⟨hm.aestronglyMeasurable, ?_⟩
    rw [HasFiniteIntegral, lintegral_prod _ hm.enorm.aemeasurable]
    simp only [uncurry_apply_pair]
    have : ∀ X g, ‖ψ (u X * g) * F g‖ₑ = ‖ψ (u X * g) * F (u X * g)‖ₑ := fun X g => by rw [hFu]
    simp_rw [this]
    rw [h.lintegral_setLIntegral_eq (H := fun g => ‖ψ g * F g‖ₑ) (hψ.mul hF).enorm
      (fun p hp g => by rw [hΛ p hp g])]
    exact ENNReal.mul_lt_top hDtop.lt_top hint
  have hzero : ∫ X in D, ∫ g in E, ψ (u X * g) * F (u X * g) ∂μ ∂ν = 0 := by
    simp_rw [hFu]
    rw [integral_integral_swap hI]
    simp_rw [integral_mul_const, hct, zero_mul, integral_zero]
  rw [hzero] at key
  have hne : ((ν D).toReal : ℂ) ≠ 0 := by
    exact_mod_cast (ENNReal.toReal_pos hD0 hDtop).ne'
  exact (mul_eq_zero.1 key.symm).resolve_left hne

end Hyp

end Integral

end Unfold

end

end GroundTheory.Automorphic.GJGlobal
