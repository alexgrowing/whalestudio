import Mathlib
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.BruhatFunctionExistsClosedSubgroup

open MeasureTheory Topology
open scoped ENNReal

noncomputable section

namespace GlobalTheory.Tw

section Defs
variable {G : Type} [Group G] [MeasurableSpace G]

abbrev RCoset (T : Subgroup G) : Type := Quotient (QuotientGroup.rightRel T)

def IsQuotMeasure (T : Subgroup G) (μ : Measure G) (μT : Measure T) (ν : Measure (RCoset T)) : Prop :=
  ∀ f : G → ℝ≥0∞, Measurable f → ∫⁻ g, f g ∂μ = ∫⁻ c, ∫⁻ t : T, f (t * Quotient.out c) ∂μT ∂ν

def IsCosetCutoff (T : Subgroup G) (μT : Measure T) (β : G → NNReal) : Prop :=
  Measurable β ∧ ∀ x, ∫⁻ t : T, β (t * x) ∂μT = 1

def quotMeas (T : Subgroup G) (μ : Measure G) (μT : Measure T) : Measure (RCoset T) :=
  Classical.epsilon (IsQuotMeasure T μ μT)

def quotInt {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] (T : Subgroup G) (μ : Measure G) (μT : Measure T)
    (F : G → E) : E :=
  ∫ c, F (Quotient.out c) ∂quotMeas T μ μT

def QuotIntegrable {E : Type} [NormedAddCommGroup E] (T : Subgroup G) (μ : Measure G) (μT : Measure T)
    (F : G → E) : Prop :=
  Integrable (fun c : RCoset T => F (Quotient.out c)) (quotMeas T μ μT)

omit [MeasurableSpace G] in

theorem apply_out_mk {T : Subgroup G} {α : Type} {F : G → α} (hF : ∀ t ∈ T, ∀ x, F (t * x) = F x) (x : G) :
    F (Quotient.out (Quotient.mk (QuotientGroup.rightRel T) x)) = F x := by
  have h := Quotient.mk_out (s := QuotientGroup.rightRel T) x
  rw [QuotientGroup.rightRel_apply] at h
  have := hF _ h (Quotient.out (Quotient.mk (QuotientGroup.rightRel T) x))
  rw [inv_mul_cancel_right] at this
  exact this.symm

theorem measurable_comp_out {T : Subgroup G} {α : Type} [MeasurableSpace α] {F : G → α} (hm : Measurable F)
    (hF : ∀ t ∈ T, ∀ x, F (t * x) = F x) : Measurable fun c : RCoset T => F (Quotient.out c) := by
  refine measurable_from_quotient.2 ?_
  have : (fun c : RCoset T => F (Quotient.out c)) ∘ Quotient.mk'' = F := funext (apply_out_mk hF)
  rwa [this]

end Defs

section Exist
variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [SecondCountableTopology G]
  [MeasurableSpace G] [BorelSpace G] {T : Subgroup G} {μ : Measure G} {μT : Measure T}

omit [SecondCountableTopology G] in

theorem exists_isCosetCutoff [LocallyCompactSpace G] [T2Space G] (hT : IsClosed (T : Set G)) [μT.IsHaarMeasure]
    [μT.IsInvInvariant] : ∃ β : G → NNReal, Continuous β ∧ IsCosetCutoff T μT β := by
  obtain ⟨β, hc, h0, -, h1⟩ := GlobalTheory.bruhatFunctionExists_closedSubgroup G T hT μT inferInstance
  have hcont : Continuous fun x => (β x⁻¹).toNNReal := continuous_real_toNNReal.comp (hc.comp continuous_inv)
  refine ⟨fun x => (β x⁻¹).toNNReal, hcont, hcont.measurable, fun x => ?_⟩
  have hi : Integrable (fun h : T => β (x⁻¹ * h)) μT := by
    by_contra hn
    have := h1 x⁻¹
    rw [integral_undef hn] at this
    exact zero_ne_one this
  have h2 := ofReal_integral_eq_lintegral_ofReal hi (Filter.Eventually.of_forall fun h => h0 _)
  rw [h1, ENNReal.ofReal_one, ← lintegral_inv_eq_self] at h2
  rw [h2]
  simp [ENNReal.ofReal]

theorem IsCosetCutoff.isQuotMeasure [SFinite μ] [μ.IsMulLeftInvariant] [SFinite μT] [μT.IsMulLeftInvariant]
    [μT.IsInvInvariant] {β : G → NNReal} (hβ : IsCosetCutoff T μT β) :
    IsQuotMeasure T μ μT ((μ.withDensity fun x => β x).map (Quotient.mk (QuotientGroup.rightRel T))) := by
  intro f hf
  have hb : Measurable fun x => (β x : ℝ≥0∞) := hβ.1.coe_nnreal_ennreal
  have hmul : Measurable fun p : G × T => (p.2 : G) * p.1 :=
    (measurable_subtype_coe.comp measurable_snd).mul measurable_fst
  have hmul' : Measurable fun p : G × T => ((p.2⁻¹ : T) : G) * p.1 :=
    (measurable_subtype_coe.comp measurable_snd.inv).mul measurable_fst
  have : μT.IsMulRightInvariant := by
    rw [← Measure.inv_eq_self μT]; infer_instance
  have hF : Measurable fun x => ∫⁻ t : T, f (t * x) ∂μT := (hf.comp hmul).lintegral_prod_right'
  have hinv : ∀ s ∈ T, ∀ x, ∫⁻ t : T, f (t * (s * x)) ∂μT = ∫⁻ t : T, f (t * x) ∂μT := fun s hs x => by
    rw [← lintegral_mul_right_eq_self (μ := μT) (fun t : T => f (t * x)) ⟨s, hs⟩]
    simp [mul_assoc]
  have hmk : Measurable (Quotient.mk (QuotientGroup.rightRel T)) := measurable_quotient_mk''
  rw [lintegral_map (measurable_comp_out hF hinv) hmk,
    lintegral_withDensity_eq_lintegral_mul _ hb (g := fun a => ∫⁻ t : T,
      f (t * Quotient.out (Quotient.mk (QuotientGroup.rightRel T) a)) ∂μT) ((measurable_comp_out hF hinv).comp hmk)]
  have e1 : ∀ x, ((fun x => (β x : ℝ≥0∞)) * fun a => ∫⁻ t : T,
      f (t * Quotient.out (Quotient.mk (QuotientGroup.rightRel T) a)) ∂μT) x = ∫⁻ t : T, β x * f (t * x) ∂μT := fun x => by
    rw [Pi.mul_apply, apply_out_mk (F := fun x => ∫⁻ t : T, f (t * x) ∂μT) hinv, lintegral_const_mul' _ _ ENNReal.coe_ne_top]
  rw [lintegral_congr e1, lintegral_lintegral_swap ((hb.comp measurable_fst).mul (hf.comp hmul)).aemeasurable]
  have e2 : ∀ t : T, ∫⁻ x, β x * f (t * x) ∂μ = ∫⁻ x, β ((t⁻¹ : T) * x) * f x ∂μ := fun t => by
    rw [← lintegral_mul_left_eq_self (μ := μ) (fun x => β ((t⁻¹ : T) * x) * f x) t]
    simp
  rw [lintegral_congr e2,
    ← lintegral_lintegral_swap (f := fun x (t : T) => β ((t⁻¹ : T) * x) * f x)
      ((hb.comp hmul').mul (hf.comp measurable_fst)).aemeasurable]
  refine lintegral_congr fun x => ?_
  rw [lintegral_mul_const _ (f := fun t : T => (β ((t⁻¹ : T) * x) : ℝ≥0∞)) (hb.comp (hmul'.comp (measurable_prodMk_left))),
    lintegral_inv_eq_self (μ := μT) (fun t : T => (β (t * x) : ℝ≥0∞)), hβ.2, one_mul]

omit [TopologicalSpace G] [IsTopologicalGroup G] [SecondCountableTopology G] [BorelSpace G] in

theorem IsQuotMeasure.eq_map {ν : Measure (RCoset T)} (hν : IsQuotMeasure T μ μT ν) {β : G → NNReal}
    (hβ : IsCosetCutoff T μT β) :
    ν = (μ.withDensity fun x => β x).map (Quotient.mk (QuotientGroup.rightRel T)) := by
  have hb : Measurable fun x => (β x : ℝ≥0∞) := hβ.1.coe_nnreal_ennreal
  ext S hS
  have hS' : MeasurableSet (Quotient.mk (QuotientGroup.rightRel T) ⁻¹' S) := measurable_quotient_mk'' hS
  rw [Measure.map_apply measurable_quotient_mk'' hS, withDensity_apply _ hS', ← lintegral_indicator hS',
    hν _ (hb.indicator hS'), ← lintegral_indicator_one hS]
  refine lintegral_congr fun c => ?_
  have hq : ∀ t : T, Quotient.mk (QuotientGroup.rightRel T) (t * c.out) = c := fun t => by
    conv_rhs => rw [← c.out_eq]
    refine Quotient.sound (QuotientGroup.rightRel_apply.2 ?_)
    simp
  by_cases hc : c ∈ S
  · simp [Set.indicator, hq, hc, hβ.2]
  · simp [Set.indicator, hq, hc]

variable [LocallyCompactSpace G] [T2Space G] [SFinite μ] [μ.IsMulLeftInvariant] [μT.IsHaarMeasure] [μT.IsInvInvariant]

theorem isQuotMeasure_quotMeas (hT : IsClosed (T : Set G)) : IsQuotMeasure T μ μT (quotMeas T μ μT) := by
  obtain ⟨β, -, hβ⟩ := exists_isCosetCutoff (μT := μT) hT
  have : LocallyCompactSpace T := hT.locallyCompactSpace
  have : SecondCountableTopology T := TopologicalSpace.Subtype.secondCountableTopology (T : Set G)
  exact Classical.epsilon_spec ⟨_, hβ.isQuotMeasure⟩

theorem IsQuotMeasure.eq_quotMeas (hT : IsClosed (T : Set G)) {ν : Measure (RCoset T)} (hν : IsQuotMeasure T μ μT ν) :
    ν = quotMeas T μ μT := by
  obtain ⟨β, -, hβ⟩ := exists_isCosetCutoff (μT := μT) hT
  rw [hν.eq_map hβ, (isQuotMeasure_quotMeas hT).eq_map hβ]

theorem quotInt_eq_cutoff (hT : IsClosed (T : Set G)) {β : G → NNReal} (hβ : IsCosetCutoff T μT β) {F : G → ℂ}
    (hm : Measurable F) (hF : ∀ t ∈ T, ∀ x, F (t * x) = F x) : quotInt T μ μT F = ∫ x, (β x : ℝ) • F x ∂μ := by
  rw [quotInt, (isQuotMeasure_quotMeas hT).eq_map hβ,
    integral_map measurable_quotient_mk''.aemeasurable (measurable_comp_out hm hF).aestronglyMeasurable,
    integral_withDensity_eq_integral_smul hβ.1]
  exact integral_congr_ae (Filter.Eventually.of_forall fun x => by simp only [apply_out_mk hF]; rfl)

theorem quotIntegrable_iff_cutoff (hT : IsClosed (T : Set G)) {β : G → NNReal} (hβ : IsCosetCutoff T μT β) {F : G → ℂ}
    (hm : Measurable F) (hF : ∀ t ∈ T, ∀ x, F (t * x) = F x) :
    QuotIntegrable T μ μT F ↔ Integrable (fun x => (β x : ℝ) • F x) μ := by
  rw [QuotIntegrable, (isQuotMeasure_quotMeas hT).eq_map hβ,
    integrable_map_measure (measurable_comp_out hm hF).aestronglyMeasurable measurable_quotient_mk''.aemeasurable,
    integrable_withDensity_iff_integrable_smul hβ.1]
  exact integrable_congr (Filter.Eventually.of_forall fun x => by simp only [Function.comp, apply_out_mk hF]; rfl)

theorem quotInt_of_isCompact (hT : IsCompact (T : Set G)) {F : G → ℂ} (hm : Measurable F)
    (hF : ∀ t ∈ T, ∀ x, F (t * x) = F x) : quotInt T μ μT F = ((μT.real Set.univ : ℝ) : ℂ)⁻¹ * ∫ x, F x ∂μ := by
  have : CompactSpace T := isCompact_iff_compactSpace.1 hT
  have h0 : μT Set.univ ≠ 0 := (isOpen_univ.measure_pos μT ⟨1, trivial⟩).ne'
  have h1 : μT Set.univ ≠ ⊤ := measure_ne_top _ _
  have hβ : IsCosetCutoff T μT fun _ => (μT Set.univ).toNNReal⁻¹ := ⟨measurable_const, fun x => by
    rw [lintegral_const, ENNReal.coe_inv (ENNReal.toNNReal_ne_zero.2 ⟨h0, h1⟩), ENNReal.coe_toNNReal h1,
      ENNReal.inv_mul_cancel h0 h1]⟩
  rw [quotInt_eq_cutoff hT.isClosed hβ hm hF, integral_smul]
  simp [Measure.real, ENNReal.toReal]

end Exist

example {G : Type} [Group G] [MeasurableSpace G] : IsCosetCutoff (⊥ : Subgroup G) (Measure.dirac 1) fun _ => 1 :=
  ⟨measurable_const, fun _ => by simp⟩

end GlobalTheory.Tw
