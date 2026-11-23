import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.AutomorphicRankinSelberg.VolMap
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.AutomorphicRankinSelberg.StripIm
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.AutomorphicRankinSelberg.TailFin
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.AutomorphicRankinSelberg.FdNull
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.AutomorphicRankinSelberg.FdCount
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.AutomorphicRankinSelberg.VolumeOpenPosUpperHalfPlane

noncomputable section

open MeasureTheory Set UpperHalfPlane CongruenceSubgroup UpperTheory.V.Af
open scoped MatrixGroups ENNReal

namespace UpperTheory.V.Lit.KT

def quotInt (H : Subgroup SL(2, ℤ)) (φ : ℍ → ℂ) : ℂ :=
  ∑ᶠ γ : SL(2, ℤ) ⧸ H, ∫ z in ModularGroup.fd, φ (γ.out⁻¹ • z)

private theorem fdFin' : Rs.FdFin := Rs.fdFin (Rs.stripIm Rs.volMap) Rs.volMap

private theorem contSL (γ : SL(2, ℤ)) : Continuous fun z : ℍ => γ • z :=
  continuous_const_smul (γ : GL (Fin 2) ℝ)

private theorem mpGL (g : GL (Fin 2) ℝ) : MeasurePreserving (fun z : ℍ => g • z) volume volume := by
  have hc : Continuous (fun z : ℍ => g • z) := continuous_const_smul g
  refine ⟨hc.measurable, ?_⟩
  ext s hs
  rw [Measure.map_apply hc.measurable hs]
  exact measure_preimage_smul (volume : Measure ℍ) g s

private theorem mpSL (γ : SL(2, ℤ)) : MeasurePreserving (fun z : ℍ => γ • z) volume volume :=
  mpGL (γ : GL (Fin 2) ℝ)

theorem quotInt_tower {H K : Subgroup SL(2, ℤ)} (hle : H ≤ K) [H.FiniteIndex] (φ : ℍ → ℂ)
    (hφ : ∀ γ ∈ K, ∀ z, φ (γ • z) = φ z) : quotInt H φ = (H.relIndex K : ℂ) * quotInt K φ := by
  haveI : K.FiniteIndex := Subgroup.finiteIndex_of_le hle
  haveI : Fintype (SL(2, ℤ) ⧸ H) := Fintype.ofFinite _
  haveI : Fintype (SL(2, ℤ) ⧸ K) := Fintype.ofFinite _
  haveI : Fintype (K ⧸ H.subgroupOf K) := Fintype.ofFinite _
  let F : SL(2, ℤ) → ℂ := fun γ => ∫ z in ModularGroup.fd, φ (γ⁻¹ • z)
  have hF : ∀ a b : SL(2, ℤ), (a : SL(2, ℤ) ⧸ K) = b → F a = F b := fun a b h => by
    simp only [F]
    congr 1
    funext z
    rw [← hφ _ (QuotientGroup.eq.1 h) (b⁻¹ • z), smul_smul, mul_inv_cancel_right]
  let e := Subgroup.quotientEquivProdOfLE hle
  have h1 : ∀ q : SL(2, ℤ) ⧸ H, F q.out = F (e q).1.out := fun q => by
    refine hF _ _ ?_
    rw [QuotientGroup.out_eq']
    conv_rhs => rw [← QuotientGroup.out_eq' q]
    rfl
  simp only [quotInt, finsum_eq_sum_of_fintype]
  change ∑ q : SL(2, ℤ) ⧸ H, F q.out = _ * ∑ q : SL(2, ℤ) ⧸ K, F q.out
  simp only [h1]
  rw [e.sum_comp (fun x => F x.1.out), Fintype.sum_prod_type, Finset.mul_sum]
  simp [Subgroup.relIndex, Subgroup.index, Nat.card_eq_fintype_card]

private def wt (H : Subgroup SL(2, ℤ)) (z : ℍ) : ℝ≥0∞ :=
  ∑' q : SL(2, ℤ) ⧸ H, ModularGroup.fd.indicator (fun _ => (1 : ℝ≥0∞)) (q.out • z)

private instance : Countable SL(2, ℤ) :=
  haveI : Countable (Matrix (Fin 2) (Fin 2) ℤ) := inferInstanceAs (Countable (Fin 2 → Fin 2 → ℤ))
  Subtype.countable

private instance (H : Subgroup SL(2, ℤ)) : Countable (SL(2, ℤ) ⧸ H) := QuotientGroup.mk_surjective.countable

private theorem wt_meas (H : Subgroup SL(2, ℤ)) : Measurable (wt H) :=
  Measurable.tsum fun q => (measurable_const.indicator fdFin'.1).comp (mpSL _).measurable

private theorem wt_sum (H : Subgroup SL(2, ℤ)) : ∀ᵐ z : ℍ, ∑' h : H, wt H ((h : SL(2, ℤ)) • z) = 2 := by
  have hc : Rs.FdCount := Rs.fdCount (Rs.fdNull Rs.volMap)
  have hb : Function.Bijective fun x : (SL(2, ℤ) ⧸ H) × H => x.1.out * (x.2 : SL(2, ℤ)) := by
    refine ⟨fun x y h => ?_, fun g => ?_⟩
    · have h1 : x.1 = y.1 := by
        have := congrArg (fun g : SL(2, ℤ) => (g : SL(2, ℤ) ⧸ H)) h
        simpa using this
      refine Prod.ext h1 (Subtype.ext ?_)
      simp only [h1] at h
      exact mul_left_cancel h
    · obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul H g
      exact ⟨((g : SL(2, ℤ) ⧸ H), h⁻¹), by simp [hh]⟩
  filter_upwards [hc] with z hz
  rw [← hz, ← (Equiv.ofBijective _ hb).tsum_eq, ENNReal.tsum_prod', ENNReal.tsum_comm]
  simp only [wt, Equiv.ofBijective_apply, mul_smul]

private theorem wt_indep (H : Subgroup SL(2, ℤ)) {S : Set ℍ} (hS : MeasurableSet S)
    (hi : ∀ γ ∈ H, ∀ z, γ • z ∈ S ↔ z ∈ S) {V W : ℍ → ℝ≥0∞} (hV : Measurable V) (hW : Measurable W)
    (sV : ∀ᵐ z : ℍ, ∑' h : H, V ((h : SL(2, ℤ)) • z) = 2) (sW : ∀ᵐ z : ℍ, ∑' h : H, W ((h : SL(2, ℤ)) • z) = 2) :
    ∫⁻ z in S, V z = ∫⁻ z in S, W z := by
  have a1 : ∀ {V W : ℍ → ℝ≥0∞}, Measurable V → Measurable W → (∀ᵐ z : ℍ, ∑' h : H, W ((h : SL(2, ℤ)) • z) = 2) →
      (∫⁻ z in S, V z) * 2 = ∑' h : H, ∫⁻ z, S.indicator V z * W ((h : SL(2, ℤ)) • z) := fun {V W} hV hW sW => by
    rw [← lintegral_tsum (f := fun (h : H) z => S.indicator V z * W ((h : SL(2, ℤ)) • z)) fun h => ((hV.indicator hS).mul (hW.comp (mpSL _).measurable)).aemeasurable,
      ← lintegral_indicator hS, ← lintegral_mul_const _ (hV.indicator hS)]
    refine lintegral_congr_ae ?_
    filter_upwards [sW] with z hz
    rw [ENNReal.tsum_mul_left, hz]
  refine (ENNReal.mul_left_inj (c := 2) (by simp) (by simp)).1 ?_
  rw [a1 hV hW sW, a1 hW hV sV, ← (Equiv.inv H).tsum_eq]
  refine tsum_congr fun h => ?_
  rw [← (mpSL (h : SL(2, ℤ))).lintegral_comp (f := fun z => S.indicator V z * W ((Equiv.inv H h : SL(2, ℤ)) • z)) ((hV.indicator hS).mul (hW.comp (mpSL _).measurable))]
  refine lintegral_congr fun z => ?_
  by_cases hz : z ∈ S
  · rw [indicator_of_mem hz, indicator_of_mem ((hi _ h.2 z).2 hz), mul_comm, Equiv.inv_apply, Subgroup.coe_inv, inv_smul_smul]
  · rw [indicator_of_notMem hz, indicator_of_notMem (fun h' => hz ((hi _ h.2 z).1 h')), zero_mul, zero_mul]

private def mu (H : Subgroup SL(2, ℤ)) : Measure ℍ :=
  Measure.sum fun q : SL(2, ℤ) ⧸ H => Measure.map (fun z : ℍ => q.out⁻¹ • z) (volume.restrict ModularGroup.fd)

private theorem mu_apply (H : Subgroup SL(2, ℤ)) {S : Set ℍ} (hS : MeasurableSet S) : mu H S = ∫⁻ z in S, wt H z := by
  rw [mu, Measure.sum_apply _ hS]
  simp only [wt]
  rw [lintegral_tsum (f := fun (q : SL(2, ℤ) ⧸ H) (z : ℍ) => ModularGroup.fd.indicator (fun _ => (1 : ℝ≥0∞)) (q.out • z))
    fun q => ((measurable_const.indicator fdFin'.1).comp (mpSL _).measurable).aemeasurable]
  refine tsum_congr fun q => ?_
  have hm : MeasurableSet ((fun z : ℍ => q.out • z) ⁻¹' ModularGroup.fd) := (mpSL _).measurable fdFin'.1
  have e : (fun z : ℍ => ModularGroup.fd.indicator (fun _ => (1 : ℝ≥0∞)) (q.out • z)) =
      ((fun z : ℍ => q.out • z) ⁻¹' ModularGroup.fd).indicator 1 := by
    ext z; rfl
  rw [e, lintegral_indicator_one hm, Measure.restrict_apply hm, Measure.map_apply (mpSL _).measurable hS,
    Measure.restrict_apply ((mpSL _).measurable hS),
    ← (mpSL q.out⁻¹).measure_preimage (hm.inter hS).nullMeasurableSet]
  congr 1
  ext z
  simp [and_comm]

private theorem intOn {φ : ℍ → ℂ} (hc : Continuous φ) {C : ℝ} (hb : ∀ z, ‖φ z‖ ≤ C) (γ : SL(2, ℤ)) :
    IntegrableOn (fun z : ℍ => φ (γ • z)) ModularGroup.fd :=
  Measure.integrableOn_of_bounded (M := C) fdFin'.2.ne (hc.comp (contSL γ)).aestronglyMeasurable
    (Filter.Eventually.of_forall fun _ => hb _)

private theorem quotInt_mu (H : Subgroup SL(2, ℤ)) [H.FiniteIndex] {φ : ℍ → ℂ} (hc : Continuous φ) {C : ℝ}
    (hb : ∀ z, ‖φ z‖ ≤ C) : quotInt H φ = ∫ w, w ∂(Measure.map φ (mu H)) := by
  haveI : Fintype (SL(2, ℤ) ⧸ H) := Fintype.ofFinite _
  rw [integral_map (f := fun w : ℂ => w) hc.aemeasurable aestronglyMeasurable_id, mu, Measure.sum_fintype, integral_finset_sum_measure,
    quotInt, finsum_eq_sum_of_fintype]
  · refine Finset.sum_congr rfl fun q _ => ?_
    rw [integral_map (contSL _).aemeasurable hc.aestronglyMeasurable]
  · intro q _
    exact (integrable_map_measure hc.aestronglyMeasurable (contSL _).aemeasurable).2 (intOn hc hb _)

private theorem quotInt_conj0 (H K : Subgroup SL(2, ℤ)) [H.FiniteIndex] [K.FiniteIndex] (α : GL (Fin 2) ℝ) (e : K ≃ H)
    (he : ∀ (h : K) (z : ℍ), α⁻¹ • (h : SL(2, ℤ)) • z = (e h : SL(2, ℤ)) • α⁻¹ • z)
    {φ : ℍ → ℂ} (hc : Continuous φ) {C : ℝ} (hb : ∀ z, ‖φ z‖ ≤ C) (hφ : ∀ γ ∈ K, ∀ z, φ (γ • z) = φ z) :
    quotInt H (fun z => φ (α • z)) = quotInt K φ := by
  have hc' : Continuous fun z : ℍ => φ (α • z) := hc.comp (continuous_const_smul α)
  rw [quotInt_mu H hc' (fun z => hb _), quotInt_mu K hc hb]
  congr 1
  ext T hT
  have hS : MeasurableSet (φ ⁻¹' T) := hc.measurable hT
  rw [Measure.map_apply hc'.measurable hT, Measure.map_apply hc.measurable hT, mu_apply _ (hc'.measurable hT),
    mu_apply _ hS, wt_indep K hS (fun γ hγ z => by rw [mem_preimage, mem_preimage, hφ γ hγ]) (wt_meas K)
      ((wt_meas H).comp (mpGL α⁻¹).measurable) (wt_sum K)]
  · rw [← (mpGL α).setLIntegral_comp_preimage hS ((wt_meas H).comp (mpGL α⁻¹).measurable)]
    simp only [Function.comp, inv_smul_smul]
    rfl
  · filter_upwards [(mpGL α⁻¹).quasiMeasurePreserving.ae (wt_sum H)] with z hz
    rw [← hz, ← e.tsum_eq]
    simp only [Function.comp, he]

private theorem conj_ex (H : Subgroup SL(2, ℤ)) (α : GL (Fin 2) ℝ) {h : SL(2, ℤ)} (hh : h ∈ H ⊓ conjGL H α) :
    ∃ y ∈ H ⊓ conjGL H α⁻¹, (y : GL (Fin 2) ℝ) = α * h * α⁻¹ := by
  obtain ⟨y, hy, e⟩ := mem_conjGL.1 hh.2
  exact ⟨y, ⟨hy, mem_conjGL.2 ⟨h, hh.1, by rw [e]; group⟩⟩, e⟩

private theorem quotInt_one_ne (H : Subgroup SL(2, ℤ)) [H.FiniteIndex] : quotInt H (fun _ => 1) ≠ 0 := by
  haveI : Fintype (SL(2, ℤ) ⧸ H) := Fintype.ofFinite _
  have h := Rs.fdPos Rs.volMap (fun _ => 1) continuous_const (fun _ => zero_le_one)
    (integrableOn_const fdFin'.2.ne) UpperHalfPlane.I (by simp [ModularGroup.fd]) one_pos
  rw [quotInt, finsum_eq_sum_of_fintype]
  simp at h ⊢
  exact h.ne'

theorem quotInt_conj (H : Subgroup SL(2, ℤ)) [H.FiniteIndex] (α : GL (Fin 2) ℝ) (h1 : (conjGL H α).FiniteIndex)
    (h2 : (conjGL H α⁻¹).FiniteIndex) {φ : ℍ → ℂ} (hc : Continuous φ) {C : ℝ} (hb : ∀ z, ‖φ z‖ ≤ C)
    (hφ : ∀ γ ∈ H, ∀ z, φ (γ • z) = φ z) (hα : ∀ γ ∈ H, ∀ z, φ (α • γ • z) = φ (α • z)) :
    quotInt H (fun z => φ (α • z)) = quotInt H φ := by
  have inj : ∀ x y : SL(2, ℤ), (x : GL (Fin 2) ℝ) = y → x = y := fun x y h =>
    Matrix.SpecialLinearGroup.map_intCast_injective (Matrix.SpecialLinearGroup.toGL_injective h)
  choose f hf ef using fun h : ↥(H ⊓ conjGL H α⁻¹) => conj_ex H α⁻¹ h.2
  simp only [inv_inv] at hf ef
  have hbij : Function.Bijective fun h => (⟨f h, hf h⟩ : ↥(H ⊓ conjGL H α)) := by
    refine ⟨fun x y h => Subtype.ext (inj _ _ ?_), fun x => ?_⟩
    · have h' : f x = f y := congrArg Subtype.val h
      have := ef x
      rw [h', ef y] at this
      simpa using this.symm
    · obtain ⟨y, hy, e⟩ := conj_ex H α x.2
      refine ⟨⟨y, hy⟩, Subtype.ext (inj _ _ ?_)⟩
      rw [ef, e]
      group
  have he : ∀ (h : ↥(H ⊓ conjGL H α⁻¹)) (z : ℍ),
      α⁻¹ • (h : SL(2, ℤ)) • z = (Equiv.ofBijective _ hbij h : SL(2, ℤ)) • α⁻¹ • z := fun h z => by
    change α⁻¹ • ((h : SL(2, ℤ)) : GL (Fin 2) ℝ) • z = (f h : GL (Fin 2) ℝ) • α⁻¹ • z
    rw [ef, smul_smul, smul_smul, mul_inv_cancel_right]
  have a := quotInt_conj0 _ _ α _ he hc hb fun γ hγ => hφ γ hγ.1
  have b := quotInt_conj0 _ _ α _ he (φ := fun _ => 1) continuous_const (C := 1) (by simp) fun _ _ _ => rfl
  rw [quotInt_tower inf_le_left _ hα, quotInt_tower inf_le_left _ hφ] at a
  rw [quotInt_tower (K := H) inf_le_left _ (fun _ _ _ => rfl),
    quotInt_tower (H := H ⊓ conjGL H α⁻¹) (K := H) inf_le_left _ (fun _ _ _ => rfl)] at b
  rw [mul_right_cancel₀ (quotInt_one_ne H) b] at a
  refine mul_left_cancel₀ ?_ a
  rw [Nat.cast_ne_zero]
  exact Subgroup.FiniteIndex.index_ne_zero

theorem finiteIndex_conjGL_rat (H : Subgroup SL(2, ℤ)) [H.FiniteIndex] (g : GL (Fin 2) ℚ) :
    (conjGL H (g.map (Rat.castHom ℝ))).FiniteIndex := by
  have := Subgroup.IsArithmetic.conj (H.map (Matrix.SpecialLinearGroup.mapGL ℝ)) g⁻¹
  rw [conjGL, ← map_inv]
  infer_instance

theorem quotInt_add (H : Subgroup SL(2, ℤ)) [H.FiniteIndex] {φ ψ : ℍ → ℂ} (hc : Continuous φ) {C : ℝ}
    (hb : ∀ z, ‖φ z‖ ≤ C) (hc' : Continuous ψ) {C' : ℝ} (hb' : ∀ z, ‖ψ z‖ ≤ C') :
    quotInt H (fun z => φ z + ψ z) = quotInt H φ + quotInt H ψ := by
  haveI : Fintype (SL(2, ℤ) ⧸ H) := Fintype.ofFinite _
  simp only [quotInt, finsum_eq_sum_of_fintype]
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun γ _ => integral_add (intOn hc hb _) (intOn hc' hb' _)

theorem quotInt_sum (H : Subgroup SL(2, ℤ)) [H.FiniteIndex] {ι : Type} (s : Finset ι) {φ : ι → ℍ → ℂ}
    (hc : ∀ i, Continuous (φ i)) (hb : ∀ i, ∃ C : ℝ, ∀ z, ‖φ i z‖ ≤ C) :
    quotInt H (fun z => ∑ i ∈ s, φ i z) = ∑ i ∈ s, quotInt H (φ i) := by
  haveI : Fintype (SL(2, ℤ) ⧸ H) := Fintype.ofFinite _
  simp only [quotInt, finsum_eq_sum_of_fintype]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun γ _ => integral_finset_sum _ fun i _ => intOn (hc i) (hb i).choose_spec _

theorem quotInt_mul (H : Subgroup SL(2, ℤ)) [H.FiniteIndex] (c : ℂ) (φ : ℍ → ℂ) :
    quotInt H (fun z => c * φ z) = c * quotInt H φ := by
  haveI : Fintype (SL(2, ℤ) ⧸ H) := Fintype.ofFinite _
  simp only [quotInt, finsum_eq_sum_of_fintype, Finset.mul_sum, integral_const_mul]

end UpperTheory.V.Lit.KT
