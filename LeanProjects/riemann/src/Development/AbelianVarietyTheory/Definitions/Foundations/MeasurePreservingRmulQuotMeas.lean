import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.AestronglyMeasurableQuotMeasureIffLift
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsBruhatFunctionOfClosedEmbedding
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsIsQuotientMeasureOfBruhatFunction

open MeasureTheory Set GlobalTheory.AutomorphicL2Unitary
open scoped ENNReal NNReal Topology Pointwise

noncomputable section

namespace GlobalTheory.Orb

instance secondCountable_subgroup {H : Type*} [Group H] [TopologicalSpace H] [SecondCountableTopology H]
    (T : Subgroup H) : SecondCountableTopology T := TopologicalSpace.Subtype.secondCountableTopology (T : Set H)

section Weil

variable {H : Type} [Group H] [MeasurableSpace H] (T : Subgroup H) (dt : Measure T) (dh : Measure H)

def IsQuotMeasure (ν : Measure (Quot T)) : Prop :=
  ∀ f : H → ℝ≥0∞, Measurable f → ∫⁻ g, f g ∂dh = ∫⁻ q, ∫⁻ t : T, f (t * q.out) ∂dt ∂ν

open Classical in

def quotMeas : Measure (Quot T) := if h : ∃ ν, IsQuotMeasure T dt dh ν then h.choose else 0

def quotInt (φ : H → ℂ) : ℂ := ∫ q, descend T φ q ∂quotMeas T dt dh

def HasQuotInt (φ : H → ℂ) (c : ℂ) : Prop := Integrable (descend T φ) (quotMeas T dt dh) ∧ quotInt T dt dh φ = c

variable {T dt dh}

theorem IsQuotMeasure.quotMeas {ν : Measure (Quot T)} (h : IsQuotMeasure T dt dh ν) :
    IsQuotMeasure T dt dh (quotMeas T dt dh) := by
  have h' : ∃ ν, IsQuotMeasure T dt dh ν := ⟨ν, h⟩
  rw [Orb.quotMeas, dif_pos h']
  exact h'.choose_spec

omit [MeasurableSpace H] in

theorem exists_out_eq (x : H) : ∃ t : T, (mk T x).out = t * x := by
  obtain ⟨t, ht⟩ := mk_eq_iff.1 (Quotient.out_eq (mk T x)).symm
  exact ⟨t, ht.symm⟩

theorem measurable_descend {X : Type*} [MeasurableSpace X] {φ : H → X} (h : LeftInv T φ) (hm : Measurable φ) :
    Measurable (descend T φ) :=
  measurable_from_quotient.2 (by rwa [show descend T φ ∘ Quotient.mk'' = φ from h.lift_descend])

theorem IsQuotMeasure.smul_left {ν : Measure (Quot T)} (h : IsQuotMeasure T dt dh ν) (c : ℝ≥0∞) :
    IsQuotMeasure T dt (c • dh) (c • ν) := fun f hf => by
  rw [lintegral_smul_measure, lintegral_smul_measure, h f hf]

theorem IsQuotMeasure.smul_right {ν : Measure (Quot T)} (h : IsQuotMeasure T dt dh ν) {c : ℝ≥0∞} (h0 : c ≠ 0)
    (ht : c ≠ ∞) : IsQuotMeasure T (c • dt) dh (c⁻¹ • ν) := fun f hf => by
  simp only [lintegral_smul_measure, smul_eq_mul]
  rw [lintegral_const_mul' _ _ ht, ← mul_assoc, ENNReal.inv_mul_cancel h0 ht, one_mul, h f hf]

variable [TopologicalSpace H] [IsTopologicalGroup H] [SecondCountableTopology H] [BorelSpace H]

theorem leftInv_lintegral [dt.IsMulRightInvariant] (f : H → ℝ≥0∞) :
    LeftInv T fun x => ∫⁻ t : T, f (t * x) ∂dt := fun s hs x => by
  simpa [mul_assoc] using lintegral_mul_right_eq_self (μ := dt) (fun t : T => f (t * x)) ⟨s, hs⟩

theorem leftInv_integral [dt.IsMulRightInvariant] (f : H → ℂ) :
    LeftInv T fun x => ∫ t : T, f (t * x) ∂dt := fun s hs x => by
  simpa [mul_assoc] using integral_mul_right_eq_self (μ := dt) (fun t : T => f (t * x)) ⟨s, hs⟩

theorem measurable_fiber [SFinite dt] {f : H → ℝ≥0∞} (hf : Measurable f) :
    Measurable fun x => ∫⁻ t : T, f (t * x) ∂dt :=
  (hf.comp ((measurable_subtype_coe.comp measurable_fst).mul measurable_snd)).lintegral_prod_left'

theorem IsQuotMeasure.eq_map {ν : Measure (Quot T)} (h : IsQuotMeasure T dt dh ν) {b : H → ℝ≥0∞}
    (hb : Measurable b) (h1 : ∀ x, ∫⁻ t : T, b (t * x) ∂dt = 1) : ν = (dh.withDensity b).map (mk T) := by
  ext A hA
  have hA' := measurable_mk hA
  rw [Measure.map_apply measurable_mk hA, withDensity_apply _ hA', ← lintegral_indicator hA',
    h _ (hb.indicator hA'), ← lintegral_indicator_one hA]
  refine lintegral_congr fun q => ?_
  have e : ∀ t : T, mk T (t * q.out) = q := fun t => (mk_mul _ _).trans (Quotient.out_eq q)
  by_cases hq : q ∈ A <;> simp [Set.indicator, e, hq, h1]

variable [LocallyCompactSpace H] [T2Space H]

theorem exists_bruhat (hT : IsClosed (T : Set H)) (dt : Measure T) [dt.IsHaarMeasure] [dt.IsMulRightInvariant] :
    ∃ b : H → ℝ≥0∞, Measurable b ∧ ∀ x, ∫⁻ t : T, b (t * x) ∂dt = 1 := by
  haveI : LocallyCompactSpace T := hT.locallyCompactSpace
  haveI := GlobalTheory.SqIntRep.isInvInvariant_of_unimodular dt
  exact GlobalTheory.exists_bruhat_function_closedEmbedding H T T.subtype hT.isClosedEmbedding_subtypeVal dt

variable (hT : IsClosed (T : Set H)) [dt.IsHaarMeasure] [dt.IsMulRightInvariant]
include hT

theorem IsQuotMeasure.unique {ν ν' : Measure (Quot T)} (h : IsQuotMeasure T dt dh ν)
    (h' : IsQuotMeasure T dt dh ν') : ν = ν' := by
  obtain ⟨b, hb, h1⟩ := exists_bruhat hT dt
  rw [h.eq_map hb h1, h'.eq_map hb h1]

theorem IsQuotMeasure.eq_quotMeas {ν : Measure (Quot T)} (h : IsQuotMeasure T dt dh ν) : ν = Orb.quotMeas T dt dh :=
  h.unique hT h.quotMeas

variable (dt dh) in

theorem isQuotMeasure_quotMeas [SFinite dh] [dh.IsMulLeftInvariant] : IsQuotMeasure T dt dh (quotMeas T dt dh) := by
  obtain ⟨b, hb, h1⟩ := exists_bruhat hT dt
  haveI : LocallyCompactSpace T := hT.locallyCompactSpace
  haveI := GlobalTheory.SqIntRep.isInvInvariant_of_unimodular dt
  have key : ∀ S : Subgroup H, S = T.subtype.range → ∃ ν : Measure (Quot S),
      ∀ f : H → ℝ≥0∞, Measurable f → ∫⁻ g, f g ∂dh = ∫⁻ q, ∫⁻ t : T, f (t * q.out) ∂dt ∂ν := by
    rintro S rfl
    exact GlobalTheory.exists_isQuotientMeasure_of_bruhatFunction H T T.subtype measurable_subtype_coe dh dt b hb h1
  obtain ⟨ν, hν⟩ := key T (T.range_subtype).symm
  exact IsQuotMeasure.quotMeas hν

variable [SFinite dh] [dh.IsMulLeftInvariant]

theorem quotMeas_smul_left (c : ℝ≥0∞) : quotMeas T dt (c • dh) = c • quotMeas T dt dh :=
  (((isQuotMeasure_quotMeas dt dh hT).smul_left c).eq_quotMeas hT).symm

theorem quotMeas_smul_right {c : ℝ≥0} (h0 : c ≠ 0) : quotMeas T (c • dt) dh = c⁻¹ • quotMeas T dt dh := by
  haveI := Measure.IsHaarMeasure.nnreal_smul dt h0
  have := (isQuotMeasure_quotMeas dt dh hT).smul_right (c := c) (by simpa using h0) ENNReal.coe_ne_top
  rw [← ENNReal.coe_inv h0] at this
  exact (IsQuotMeasure.eq_quotMeas (dt := c • dt) hT this).symm

theorem measurePreserving_rmul_quotMeas [dh.IsMulRightInvariant] (g : H) :
    MeasurePreserving (rmul T g) (quotMeas T dt dh) (quotMeas T dt dh) := by
  haveI : LocallyCompactSpace T := hT.locallyCompactSpace
  have hm : Measurable (rmul T g) := measurable_from_quotient.2 (measurable_mk.comp (measurable_mul_const g))
  refine ⟨hm, IsQuotMeasure.eq_quotMeas hT fun f hf => ?_⟩
  have hi := leftInv_lintegral (dt := dt) f
  rw [← lintegral_mul_right_eq_self f g, isQuotMeasure_quotMeas dt dh hT (fun x => f (x * g)) (hf.comp (measurable_mul_const g))]
  refine ((lintegral_map (measurable_descend hi (measurable_fiber hf)) hm).trans (lintegral_congr fun q => ?_)).symm
  conv_lhs => rw [← Quotient.out_eq q]
  exact (hi.descend_mk (q.out * g)).trans (by simp only [mul_assoc])

theorem weil_integral {f : H → ℂ} (hf : Integrable f dh) :
    (∀ᵐ q ∂quotMeas T dt dh, Integrable (fun t : T => f (t * q.out)) dt) ∧
      HasQuotInt T dt dh (fun x => ∫ t : T, f (t * x) ∂dt) (∫ g, f g ∂dh) := by
  haveI : LocallyCompactSpace T := hT.locallyCompactSpace
  obtain ⟨b, hb, h1⟩ := exists_bruhat hT dt
  have hW := isQuotMeasure_quotMeas dt dh hT
  have hν := hW.eq_map hb h1
  have hΦ : Measurable fun p : H × T => (p.2 : H) * p.1 :=
    (measurable_subtype_coe.comp measurable_snd).mul measurable_fst
  have hP : MeasurePreserving (fun p : H × T => (p.2 : H) * p.1) ((dh.withDensity b).prod dt) dh := by
    refine ⟨hΦ, Measure.ext_of_lintegral _ fun φ hφ => ?_⟩
    have hi := leftInv_lintegral (dt := dt) φ
    rw [lintegral_map hφ hΦ, lintegral_prod (fun p : H × T => φ (p.2 * p.1)) (hφ.comp hΦ).aemeasurable, hW φ hφ, hν]
    refine ((lintegral_map (measurable_descend hi (measurable_fiber hφ)) measurable_mk).trans ?_).symm
    simp only [hi.descend_mk]
  have hm := hf.1.stronglyMeasurable_mk
  set f' := hf.1.mk f
  have hff : f =ᵐ[dh] f' := hf.1.ae_eq_mk
  obtain ⟨N, hN, hNm, hN0⟩ := exists_measurable_superset_of_null hff
  have hae : ∀ᵐ q ∂quotMeas T dt dh, (fun t : T => f (t * q.out)) =ᵐ[dt] fun t : T => f' (t * q.out) := by
    have h2 := hW (N.indicator 1) (measurable_one.indicator hNm)
    rw [lintegral_indicator_one hNm, hN0] at h2
    filter_upwards [(lintegral_eq_zero_iff (measurable_descend (leftInv_lintegral (dt := dt) _)
      (measurable_fiber (measurable_one.indicator hNm)))).1 h2.symm] with q hq
    have h3 := (lintegral_eq_zero_iff (f := fun t : T => N.indicator (1 : H → ℝ≥0∞) (t * q.out))
      ((measurable_one.indicator hNm).comp (measurable_subtype_coe.mul_const _))).1 hq
    filter_upwards [h3] with t ht
    by_contra hne
    simp [Set.indicator_of_mem (hN hne)] at ht
  have hf' : Integrable f' dh := hf.congr hff
  have hI := hP.integrable_comp_of_integrable hf'
  have hi := leftInv_integral (dt := dt) f'
  have hFm : Measurable fun x => ∫ t : T, f' (t * x) ∂dt :=
    (StronglyMeasurable.integral_prod_right' (hm.comp_measurable hΦ)).measurable
  have hD := (measurable_descend hi hFm).aestronglyMeasurable (μ := (dh.withDensity b).map (mk T))
  have e : descend T (fun x => ∫ t : T, f (t * x) ∂dt) =ᵐ[quotMeas T dt dh]
      descend T fun x => ∫ t : T, f' (t * x) ∂dt := hae.mono fun q hq => integral_congr_ae hq
  refine ⟨?_, Integrable.congr ?_ e.symm, ?_⟩
  · have h2 := hW _ hm.measurable.enorm
    have h3 := ae_lt_top (measurable_descend (leftInv_lintegral (dt := dt) _) (measurable_fiber hm.measurable.enorm))
      (h2 ▸ hf'.2.ne :)
    filter_upwards [hae, h3] with q hq h4
    exact Integrable.congr ⟨(hm.comp_measurable (measurable_subtype_coe.mul_const _)).aestronglyMeasurable, h4⟩ hq.symm
  · rw [hν, integrable_map_measure hD measurable_mk.aemeasurable]
    exact hI.integral_prod_left.congr (.of_forall fun x => (hi.descend_mk x).symm)
  · rw [quotInt, integral_congr_ae e, hν, integral_map measurable_mk.aemeasurable hD, integral_congr_ae hff]
    conv_rhs => rw [← hP.map_eq, integral_map hΦ.aemeasurable hm.aestronglyMeasurable]
    simp only [hi.descend_mk]
    exact (integral_prod _ hI).symm

theorem quotMeas_image_lt_top [IsFiniteMeasureOnCompacts dh] {C : Set H} (hC : IsCompact C) :
    quotMeas T dt dh (mk T '' C) < ∞ := by
  haveI : LocallyCompactSpace T := hT.locallyCompactSpace
  obtain ⟨U, hU, hU1⟩ := exists_compact_mem_nhds (1 : T)
  have hK : IsCompact (((↑) : T → H) '' U * C) := (hU.image continuous_subtype_val).mul hC
  have hm : Measurable ((((↑) : T → H) '' U * C).indicator (1 : H → ℝ≥0∞)) := measurable_one.indicator hK.measurableSet
  have hi := leftInv_lintegral (dt := dt) ((((↑) : T → H) '' U * C).indicator (1 : H → ℝ≥0∞))
  have h1 := mul_meas_ge_le_lintegral₀ (μ := quotMeas T dt dh)
    (measurable_descend hi (measurable_fiber hm)).aemeasurable (dt U)
  have h2 := isQuotMeasure_quotMeas dt dh hT _ hm
  rw [lintegral_indicator_one hK.measurableSet] at h2
  have h3 := ENNReal.lt_top_of_mul_ne_top_right ((h1.trans_eq h2.symm).trans_lt hK.measure_lt_top).ne
    (Measure.measure_pos_of_mem_nhds dt hU1).ne'
  refine (measure_mono ?_).trans_lt h3
  rintro _ ⟨x, hx, rfl⟩
  rw [mem_setOf_eq, hi.descend_mk, ← lintegral_indicator_one hU.measurableSet]
  refine lintegral_mono fun t => ?_
  by_cases ht : t ∈ U
  · rw [indicator_of_mem ht, indicator_of_mem (Set.mul_mem_mul (mem_image_of_mem _ ht) hx)]; rfl
  · simp [ht]

theorem integrable_descend [IsFiniteMeasureOnCompacts dh] {φ : H → ℂ} (hi : LeftInv T φ) (hc : Continuous φ)
    {C : Set H} (hC : IsCompact C) (h0 : ∀ x, φ x ≠ 0 → ∃ t ∈ T, t * x ∈ C) :
    Integrable (descend T φ) (quotMeas T dt dh) := by
  obtain ⟨M, hM⟩ := hC.exists_bound_of_continuousOn hc.continuousOn
  have hm := measurable_descend hi hc.measurable
  have hs : Function.support (descend T φ) ⊆ mk T '' C := fun q hq => by
    obtain ⟨t, ht, h⟩ := h0 _ hq
    exact ⟨_, h, (mk_mul ⟨t, ht⟩ _).trans (Quotient.out_eq q)⟩
  rw [← integrableOn_iff_integrable_of_support_subset (Subset.refl _)]
  refine Measure.integrableOn_of_bounded (M := M)
    ((measure_mono hs).trans_lt (quotMeas_image_lt_top hT hC)).ne hm.aestronglyMeasurable ?_
  filter_upwards [ae_restrict_mem (measurableSet_support hm)] with q hq
  obtain ⟨x, hx, rfl⟩ := hs hq
  rw [hi.descend_mk]
  exact hM x hx

theorem quotMeas_of_finite [IsFiniteMeasure dt] : quotMeas T dt dh = (dt univ)⁻¹ • dh.map (mk T) := by
  have h0 : dt univ ≠ 0 := (isOpen_univ.measure_pos dt univ_nonempty).ne'
  rw [(isQuotMeasure_quotMeas dt dh hT).eq_map (b := fun _ => (dt univ)⁻¹) measurable_const
    fun x => by rw [lintegral_const, ENNReal.inv_mul_cancel h0 (measure_ne_top _ _)], withDensity_const,
    Measure.map_smul]

theorem hasQuotInt_of_finite [IsFiniteMeasure dt] {φ : H → ℂ} (hi : LeftInv T φ) (hφ : Integrable φ dh) :
    HasQuotInt T dt dh φ ((∫ g, φ g ∂dh) / dt.real univ) := by
  have h0 : (dt.real univ : ℂ) ≠ 0 := by
    exact_mod_cast ENNReal.toReal_ne_zero.2 ⟨(isOpen_univ.measure_pos dt univ_nonempty).ne', measure_ne_top _ _⟩
  have h := (weil_integral (dt := dt) hT hφ).2
  have e : (fun x => ∫ t : T, φ (t * x) ∂dt) = fun x => (dt.real univ : ℂ) * φ x := funext fun x => by
    simp [fun t : T => hi t t.2 x]
  rw [e] at h
  refine ⟨(integrable_const_mul_iff (IsUnit.mk0 _ h0) _).1 h.1, ?_⟩
  rw [eq_div_iff h0, ← h.2, mul_comm]
  exact (integral_const_mul _ _).symm

end Weil

section Transport

variable {H H' : Type} [Group H] [Group H'] [TopologicalSpace H] [TopologicalSpace H']

def subEquiv (e : H ≃ₜ* H') {T : Subgroup H} {T' : Subgroup H'} (h : ∀ x, e x ∈ T' ↔ x ∈ T) : T ≃ₜ* T' where
  toFun t := ⟨e t, (h _).2 t.2⟩
  invFun t := ⟨e.symm t, (h _).1 (by rw [e.apply_symm_apply]; exact t.2)⟩
  left_inv t := Subtype.ext (e.symm_apply_apply _)
  right_inv t := Subtype.ext (e.apply_symm_apply _)
  map_mul' s t := Subtype.ext (map_mul e _ _)
  continuous_toFun := (e.continuous.comp continuous_subtype_val).subtype_mk _
  continuous_invFun := (e.symm.continuous.comp continuous_subtype_val).subtype_mk _

def quotMap (e : H ≃ₜ* H') {T : Subgroup H} {T' : Subgroup H'} (h : ∀ x, e x ∈ T' ↔ x ∈ T) : Quot T → Quot T' :=
  Quotient.map' e fun x y hxy => by
    rw [QuotientGroup.rightRel_apply] at hxy ⊢
    simpa using (h _).2 hxy

variable [IsTopologicalGroup H] [SecondCountableTopology H] [LocallyCompactSpace H] [T2Space H] [MeasurableSpace H]
  [BorelSpace H] [IsTopologicalGroup H'] [SecondCountableTopology H'] [LocallyCompactSpace H'] [T2Space H']
  [MeasurableSpace H'] [BorelSpace H'] (e : H ≃ₜ* H') {T : Subgroup H} {T' : Subgroup H'}
  (h : ∀ x, e x ∈ T' ↔ x ∈ T) (hT : IsClosed (T : Set H)) (dt : Measure T) [dt.IsHaarMeasure]
  [dt.IsMulRightInvariant] (dh : Measure H) [SFinite dh] [dh.IsMulLeftInvariant]

omit [SecondCountableTopology H] [LocallyCompactSpace H] [T2Space H] [SecondCountableTopology H']
  [LocallyCompactSpace H'] [T2Space H'] in

instance isMulRightInvariant_map (μ : Measure H) [μ.IsMulRightInvariant] : (μ.map e).IsMulRightInvariant :=
  ⟨fun g => by
    have he : Measurable e := (map_continuous e).measurable
    rw [Measure.map_map (measurable_mul_const g) he]
    conv_rhs => rw [← map_mul_right_eq_self μ (e.symm g)]
    rw [Measure.map_map he (measurable_mul_const _)]
    congr 1
    ext x
    simp⟩

include hT in

theorem quotMeas_map :
    quotMeas T' (dt.map (subEquiv e h)) (dh.map e) = (quotMeas T dt dh).map (quotMap e h) := by
  haveI : LocallyCompactSpace T := hT.locallyCompactSpace
  have hT' : IsClosed (T' : Set H') := by
    convert hT.preimage (map_continuous e.symm) using 1
    ext x
    simpa using h (e.symm x)
  have he : Measurable e := (map_continuous e).measurable
  have hm : Measurable (quotMap e h) := measurable_from_quotient.2 (measurable_mk.comp he)
  refine (IsQuotMeasure.eq_quotMeas hT' fun f hf => ?_).symm
  have hi := leftInv_lintegral (dt := dt.map (subEquiv e h)) f
  rw [lintegral_map hf he, isQuotMeasure_quotMeas dt dh hT (fun x => f (e x)) (hf.comp he)]
  refine ((lintegral_map (measurable_descend hi (measurable_fiber hf)) hm).trans (lintegral_congr fun q => ?_)).symm
  conv_lhs => rw [← Quotient.out_eq q]
  refine (hi.descend_mk (e q.out)).trans ?_
  rw [lintegral_map (f := fun t : T' => f (t * e q.out)) (hf.comp (measurable_subtype_coe.mul_const _))
    (map_continuous (subEquiv e h)).measurable]
  simp only [map_mul]
  rfl

omit [IsTopologicalGroup H] [SecondCountableTopology H] [LocallyCompactSpace H] [T2Space H] [IsTopologicalGroup H']
  [SecondCountableTopology H'] [LocallyCompactSpace H'] [T2Space H'] in

theorem measurableEmbedding_quotMap : MeasurableEmbedding (quotMap e h) :=
  MeasurableEquiv.measurableEmbedding
    { toFun := quotMap e h
      invFun := quotMap e.symm fun x => by simpa using (h (e.symm x)).symm
      left_inv := fun q => Quotient.inductionOn q fun x => congrArg (mk T) (e.symm_apply_apply x)
      right_inv := fun q => Quotient.inductionOn q fun x => congrArg (mk T') (e.apply_symm_apply x)
      measurable_toFun := measurable_from_quotient.2 (measurable_mk.comp e.continuous.measurable)
      measurable_invFun := measurable_from_quotient.2 (measurable_mk.comp e.symm.continuous.measurable) }

include hT in

theorem hasQuotInt_map {φ : H' → ℂ} (hi : LeftInv T' φ) (c : ℂ) :
    (HasQuotInt T' (dt.map (subEquiv e h)) (dh.map e) φ c ↔ HasQuotInt T dt dh (φ ∘ e) c) ∧
      quotInt T' (dt.map (subEquiv e h)) (dh.map e) φ = quotInt T dt dh (φ ∘ e) := by
  have e1 : descend T' φ ∘ quotMap e h = descend T (φ ∘ e) := funext fun q => by
    conv_lhs => rw [← Quotient.out_eq q]
    exact hi.descend_mk (e q.out)
  have e2 : quotInt T' (dt.map (subEquiv e h)) (dh.map e) φ = quotInt T dt dh (φ ∘ e) := by
    rw [quotInt, quotMeas_map e h hT, (measurableEmbedding_quotMap e h).integral_map, quotInt, ← e1]
    rfl
  refine ⟨and_congr ?_ (by rw [e2]), e2⟩
  rw [quotMeas_map e h hT, (measurableEmbedding_quotMap e h).integrable_map_iff, e1]

end Transport

section Orbital

variable {H : Type} [Group H]

abbrev cent (γ : H) : Subgroup H := Subgroup.centralizer {γ}

def conjFn (γ : H) (f : H → ℂ) : H → ℂ := fun x => f (x⁻¹ * γ * x)

theorem mem_cent {γ t : H} : t ∈ cent γ ↔ t * γ = γ * t := Subgroup.mem_centralizer_singleton_iff

theorem leftInv_conjFn {γ : H} {T : Subgroup H} (h : T ≤ cent γ) (f : H → ℂ) : LeftInv T (conjFn γ f) :=
  fun t ht x => by
    have : (t * x)⁻¹ * γ * (t * x) = x⁻¹ * (t⁻¹ * (γ * t)) * x := by group
    rw [conjFn, this, ← mem_cent.1 (h ht), inv_mul_cancel_left, conjFn]

def IsProperOrbit [TopologicalSpace H] (T : Subgroup H) (γ : H) : Prop :=
  ∀ K : Set H, IsCompact K → ∃ C : Set H, IsCompact C ∧ ∀ x, x⁻¹ * γ * x ∈ K → ∃ t ∈ T, t * x ∈ C

variable [MeasurableSpace H]

def orbInt (dh : Measure H) (γ : H) (dt : Measure (cent γ)) (f : H → ℂ) : ℂ := quotInt (cent γ) dt dh (conjFn γ f)

def HasOrbInt (dh : Measure H) (γ : H) (dt : Measure (cent γ)) (f : H → ℂ) (c : ℂ) : Prop :=
  HasQuotInt (cent γ) dt dh (conjFn γ f) c

def wOrbInt (T : Subgroup H) (dt : Measure T) (dh : Measure H) (γ : H) (b f : H → ℂ) : ℂ :=
  quotInt T dt dh fun x => b x * conjFn γ f x

variable {dh : Measure H} {γ : H} {dt : Measure (cent γ)} {f f' : H → ℂ} {c c' : ℂ}

theorem orbInt_def : orbInt dh γ dt f = ∫ q, f (q.out⁻¹ * γ * q.out) ∂quotMeas (cent γ) dt dh := rfl

theorem HasOrbInt.orbInt_eq (h : HasOrbInt dh γ dt f c) : orbInt dh γ dt f = c := h.2

theorem HasOrbInt.add (h : HasOrbInt dh γ dt f c) (h' : HasOrbInt dh γ dt f' c') :
    HasOrbInt dh γ dt (f + f') (c + c') :=
  ⟨h.1.add h'.1, (integral_add h.1 h'.1).trans (congrArg₂ (· + ·) h.2 h'.2)⟩

theorem HasOrbInt.smul (h : HasOrbInt dh γ dt f c) (a : ℂ) : HasOrbInt dh γ dt (a • f) (a * c) :=
  ⟨h.1.smul a, (integral_const_mul a _).trans (congrArg (a * ·) h.2)⟩

variable [TopologicalSpace H] [IsTopologicalGroup H] [T2Space H]

omit [MeasurableSpace H] in

theorem isClosed_cent (γ : H) : IsClosed (cent γ : Set H) := by
  rw [show (cent γ : Set H) = {t | t * γ = γ * t} from Set.ext fun _ => mem_cent]
  exact isClosed_eq (by fun_prop) (by fun_prop)

omit [MeasurableSpace H] in

theorem isProperOrbit_of_isClosed [LocallyCompactSpace H] [SecondCountableTopology H]
    (h : IsClosed (range fun x : H => x⁻¹ * γ * x)) : IsProperOrbit (cent γ) γ := by
  intro K hK
  let X := range fun x : H => x⁻¹ * γ * x
  letI : MulAction H X :=
    { smul := fun g y => ⟨g * y * g⁻¹, by
        obtain ⟨_, x, rfl⟩ := y
        exact ⟨x * g⁻¹, by group⟩⟩
      one_smul := fun y => Subtype.ext (show 1 * y.1 * 1⁻¹ = y by group)
      mul_smul := fun a b y => Subtype.ext (show a * b * y.1 * (a * b)⁻¹ = a * (b * y.1 * b⁻¹) * a⁻¹ by group) }
  haveI : ContinuousSMul H X :=
    ⟨Continuous.subtype_mk (f := fun p : H × X => p.1 * p.2.1 * p.1⁻¹) (by fun_prop) _⟩
  haveI : MulAction.IsPretransitive H X := ⟨by
    rintro ⟨_, x, rfl⟩ ⟨_, y, rfl⟩
    exact ⟨y⁻¹ * x, Subtype.ext (show y⁻¹ * x * (x⁻¹ * γ * x) * (y⁻¹ * x)⁻¹ = y⁻¹ * γ * y by group)⟩⟩
  haveI : LocallyCompactSpace X := h.locallyCompactSpace
  let o : X := ⟨γ, 1, by simp⟩
  have ho : IsOpenMap fun g : H => g • o := isOpenMap_smul_of_sigmaCompact o
  have hK' : IsCompact (((↑) : X → H) ⁻¹' K) := h.isClosedEmbedding_subtypeVal.isCompact_preimage hK
  obtain ⟨n, hn⟩ := hK'.elim_directed_cover
    (fun n => (fun g : H => g • o) '' interior (CompactExhaustion.choice H n))
    (fun n => ho _ isOpen_interior) (fun y _ => by
      obtain ⟨g, rfl⟩ := MulAction.exists_smul_eq H o y
      obtain ⟨n, hn⟩ := (CompactExhaustion.choice H).exists_mem g
      exact mem_iUnion.2 ⟨n + 1, g, (CompactExhaustion.choice H).subset_interior_succ n hn, rfl⟩)
    (Monotone.directed_le fun a b hab => image_mono (interior_mono ((CompactExhaustion.choice H).subset hab)))
  refine ⟨_, ((CompactExhaustion.choice H).isCompact n).inv, fun x hx => ?_⟩
  obtain ⟨g, hg, e⟩ := hn (a := ⟨_, x, rfl⟩) hx
  have e' : g * γ * g⁻¹ = x⁻¹ * γ * x := congrArg Subtype.val e
  refine ⟨g⁻¹ * x⁻¹, mem_cent.2 ?_, by simpa using interior_subset hg⟩
  calc g⁻¹ * x⁻¹ * γ = g⁻¹ * (x⁻¹ * γ * x) * x⁻¹ := by group
    _ = _ := by rw [← e']; group

variable [LocallyCompactSpace H] [SecondCountableTopology H] [BorelSpace H] [dh.IsHaarMeasure] [dt.IsHaarMeasure]
  [dt.IsMulRightInvariant]

theorem IsProperOrbit.hasOrbInt (h : IsProperOrbit (cent γ) γ) (hf : Continuous f) (hc : HasCompactSupport f) :
    HasOrbInt dh γ dt f (orbInt dh γ dt f) := by
  obtain ⟨C, hC, h0⟩ := h _ hc
  exact ⟨integrable_descend (isClosed_cent γ) (leftInv_conjFn le_rfl f) (hf.comp (by fun_prop)) hC
    fun x hx => h0 x (subset_tsupport f hx), rfl⟩

theorem hasOrbInt_of_finite [IsFiniteMeasure dt] (hf : Integrable (conjFn γ f) dh) :
    HasOrbInt dh γ dt f ((∫ x, f (x⁻¹ * γ * x) ∂dh) / dt.real univ) :=
  hasQuotInt_of_finite (isClosed_cent γ) (leftInv_conjFn le_rfl f) hf

theorem orbInt_smul_left (a : ℝ≥0) : orbInt (a • dh) γ dt f = a * orbInt dh γ dt f := by
  rw [orbInt_def, show a • dh = (a : ℝ≥0∞) • dh from rfl, quotMeas_smul_left (isClosed_cent γ), integral_smul_measure]
  simp [orbInt_def]

omit [MeasurableSpace H] [IsTopologicalGroup H] [T2Space H] [LocallyCompactSpace H] [SecondCountableTopology H]
  [BorelSpace H] in

def centEquiv {H' : Type} [Group H'] [TopologicalSpace H'] (e : H ≃ₜ* H') (γ : H) {γ' : H'} (h : e γ = γ') :
    cent γ ≃ₜ* cent γ' :=
  subEquiv e fun x => by rw [mem_cent, mem_cent, ← h, ← map_mul, ← map_mul, e.injective.eq_iff]

theorem hasOrbInt_map {H' : Type} [Group H'] [TopologicalSpace H'] [IsTopologicalGroup H']
    [SecondCountableTopology H'] [LocallyCompactSpace H'] [T2Space H'] [MeasurableSpace H'] [BorelSpace H']
    (e : H ≃ₜ* H') {γ' : H'} (h : e γ = γ') (f : H' → ℂ) (c : ℂ) :
    (HasOrbInt (dh.map e) γ' (dt.map (centEquiv e γ h)) f c ↔ HasOrbInt dh γ dt (f ∘ e) c) ∧
      orbInt (dh.map e) γ' (dt.map (centEquiv e γ h)) f = orbInt dh γ dt (f ∘ e) := by
  have e1 : conjFn γ' f ∘ e = conjFn γ (f ∘ e) := funext fun x => by simp [conjFn, h]
  have := hasQuotInt_map e (T := cent γ) (T' := cent γ')
    (fun x => by rw [mem_cent, mem_cent, ← h, ← map_mul, ← map_mul, e.injective.eq_iff])
    (isClosed_cent γ) dt dh (leftInv_conjFn le_rfl f) c
  rwa [e1] at this

omit [MeasurableSpace H] [T2Space H] [LocallyCompactSpace H] [SecondCountableTopology H] [BorelSpace H] in

def conjEquiv (g : H) : H ≃ₜ* H :=
  { MulAut.conj g with
    continuous_toFun := (continuous_const.mul continuous_id).mul continuous_const
    continuous_invFun := (continuous_const.mul continuous_id).mul continuous_const }

theorem hasOrbInt_conj [dh.IsMulRightInvariant] (g : H) {γ' : H} (h : g * γ * g⁻¹ = γ') (f : H → ℂ) (c : ℂ) :
    (HasOrbInt dh γ' (dt.map (centEquiv (conjEquiv g) γ h)) f c ↔ HasOrbInt dh γ dt f c) ∧
      orbInt dh γ' (dt.map (centEquiv (conjEquiv g) γ h)) f = orbInt dh γ dt f := by
  have h1 := hasOrbInt_map (dh := dh) (dt := dt) (conjEquiv g) h f c
  have h2 : dh.map (conjEquiv g) = dh := by
    have : (conjEquiv g : H → H) = (· * g⁻¹) ∘ (g * ·) := rfl
    rw [this, ← Measure.map_map (measurable_mul_const _) (measurable_const_mul _), map_mul_left_eq_self,
      map_mul_right_eq_self]
  let r : Quot (cent γ) ≃ᵐ Quot (cent γ) :=
    { toFun := rmul _ g⁻¹
      invFun := rmul _ g
      left_inv := fun q => by rw [← rmul_mul, inv_mul_cancel, rmul_one]
      right_inv := fun q => by rw [← rmul_mul, mul_inv_cancel, rmul_one]
      measurable_toFun := (measurePreserving_rmul_quotMeas (dt := dt) (dh := dh) (isClosed_cent γ) _).measurable
      measurable_invFun := (measurePreserving_rmul_quotMeas (dt := dt) (dh := dh) (isClosed_cent γ) _).measurable }
  have hr : MeasurePreserving r (quotMeas _ dt dh) (quotMeas _ dt dh) :=
    measurePreserving_rmul_quotMeas (isClosed_cent γ) g⁻¹
  have h3 : descend (cent γ) (conjFn γ (f ∘ conjEquiv g)) = descend (cent γ) (conjFn γ f) ∘ r := funext fun q => by
    conv_rhs => rw [← Quotient.out_eq q]
    refine Eq.trans ?_ ((leftInv_conjFn le_rfl f).descend_mk (q.out * g⁻¹)).symm
    exact congrArg f (show g * _ * g⁻¹ = _ by group)
  have h4 : orbInt dh γ dt (f ∘ conjEquiv g) = orbInt dh γ dt f := by
    rw [orbInt, quotInt, h3]
    exact hr.integral_comp' _
  rw [h2, h4] at h1
  refine ⟨h1.1.trans (and_congr ?_ (by rw [← orbInt, h4, orbInt])), h1.2⟩
  rw [h3]
  exact hr.integrable_comp_emb r.measurableEmbedding

example [CompactSpace H] : HasOrbInt dh γ dt 1 (dh.real univ / dt.real univ) := by
  haveI : CompactSpace (cent γ) := isCompact_iff_compactSpace.1 (isClosed_cent γ).isCompact
  simpa using hasOrbInt_of_finite (dh := dh) (dt := dt) (f := 1) (integrable_const (1 : ℂ))

end Orbital

end GlobalTheory.Orb
