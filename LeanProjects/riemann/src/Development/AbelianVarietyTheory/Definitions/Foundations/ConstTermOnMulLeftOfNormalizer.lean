import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.AestronglyMeasurableQuotMeasureIffLift
import Development.AbelianVarietyTheory.Proofs.HeightProofs.IntegrableOnFundamentalDomainOfCocompact

open MeasureTheory Set GlobalTheory.AutomorphicL2Unitary
open scoped ENNReal Pointwise

noncomputable section

namespace GlobalTheory.Cusp

variable {G : Type} [Group G] [TopologicalSpace G] (Γ N : Subgroup G)

def Cocompact : Prop := ∃ K : Set N, IsCompact K ∧ ∀ n : N, ∃ γ ∈ Γ.subgroupOf N, γ * n ∈ K

instance discreteTopology_subgroupOf [DiscreteTopology Γ] : DiscreteTopology (Γ.subgroupOf N) :=
  .of_continuous_injective (f := fun x : Γ.subgroupOf N => (⟨x.1.1, x.2⟩ : Γ))
    ((continuous_subtype_val.comp continuous_subtype_val).subtype_mk _)
    fun _ _ h => Subtype.ext (Subtype.ext (congrArg (fun z : Γ => z.1) h))

instance secondCountable_subgroup [SecondCountableTopology G] : SecondCountableTopology N :=
  TopologicalSpace.Subtype.secondCountableTopology _

variable [IsTopologicalGroup G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] [DiscreteTopology Γ]
  [LocallyCompactSpace N]

def probMeasure : Measure (Quot (Γ.subgroupOf N)) :=
  (quotMeasure (Γ.subgroupOf N) Measure.haar univ)⁻¹ • quotMeasure (Γ.subgroupOf N) Measure.haar

def constTermOn (φ : G → ℂ) (x : G) : ℂ := ∫ q, φ ((q.out : N) * x) ∂probMeasure Γ N

variable {Γ N} {φ ψ : G → ℂ} {μ : Measure N} {𝓕 : Set N}

omit [TopologicalSpace G] [IsTopologicalGroup G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
  [DiscreteTopology Γ] [LocallyCompactSpace N] in

theorem leftInv_integrand (hφ : LeftInv Γ φ) (x : G) : LeftInv (Γ.subgroupOf N) fun n : N => φ (n * x) :=
  fun γ hγ n => by simp only [Subgroup.coe_mul, mul_assoc]; exact hφ _ hγ _

theorem probMeasure_eq (μ : Measure N) [μ.IsHaarMeasure] :
    probMeasure Γ N = (quotMeasure (Γ.subgroupOf N) μ univ)⁻¹ • quotMeasure (Γ.subgroupOf N) μ := by
  have h0 : ((Measure.haarScalarFactor μ Measure.haar : NNReal) : ℝ≥0∞) ≠ 0 :=
    ENNReal.coe_ne_zero.2 (Measure.haarScalarFactor_pos_of_isHaarMeasure μ Measure.haar).ne'
  conv_rhs => rw [Measure.isMulLeftInvariant_eq_smul μ Measure.haar]
  rw [ENNReal.smul_def, quotMeasure_smul, smul_smul, Measure.smul_apply, smul_eq_mul,
    ENNReal.mul_inv (Or.inl h0) (Or.inl ENNReal.coe_ne_top), mul_right_comm, ENNReal.inv_mul_cancel h0 ENNReal.coe_ne_top,
    one_mul, probMeasure]

theorem constTermOn_eq [μ.IsHaarMeasure] (h : IsFundamentalDomain (Γ.subgroupOf N) 𝓕 μ) (hφ : LeftInv Γ φ) (x : G) :
    constTermOn Γ N φ x = (μ.real 𝓕)⁻¹ • ∫ n in 𝓕, φ (n * x) ∂μ := by
  rw [constTermOn, probMeasure_eq μ, integral_smul_measure, quotMeasure_univ h, integral_quotMeasure h,
    ENNReal.toReal_inv, measureReal_def]
  exact congrArg _ (integral_congr_ae (.of_forall (leftInv_integrand hφ x).descend_mk))

theorem constTermOn_eq_of_measure_eq_one [μ.IsHaarMeasure] (h : IsFundamentalDomain (Γ.subgroupOf N) 𝓕 μ)
    (h1 : μ 𝓕 = 1) (hφ : LeftInv Γ φ) (x : G) : constTermOn Γ N φ x = ∫ n in 𝓕, φ (n * x) ∂μ := by
  simp [constTermOn_eq h hφ, measureReal_def, h1]

theorem constTermOn_mul_right (φ : G → ℂ) (x g : G) :
    constTermOn Γ N (fun y => φ (y * g)) x = constTermOn Γ N φ (x * g) := by
  simp only [constTermOn, mul_assoc]

theorem constTermOn_smul (c : ℂ) (φ : G → ℂ) (x : G) : constTermOn Γ N (c • φ) x = c * constTermOn Γ N φ x :=
  integral_const_mul c _

theorem constTermOn_mul_left_of_normalizer (hφ : LeftInv Γ φ) {γ : G} (hγ : γ ∈ Γ)
    (hN : ∀ n, n ∈ N ↔ γ * n * γ⁻¹ ∈ N) (x : G) : constTermOn Γ N φ (γ * x) = constTermOn Γ N φ x := by
  let e : N ≃ₜ* N :=
    { toFun := fun n => ⟨γ * n * γ⁻¹, (hN _).1 n.2⟩
      invFun := fun n => ⟨γ⁻¹ * n * γ, (hN _).2 (by simp [mul_assoc])⟩
      left_inv := fun n => by simp [mul_assoc]
      right_inv := fun n => by simp [mul_assoc]
      map_mul' := fun a b => by simp [mul_assoc]
      continuous_toFun := by fun_prop
      continuous_invFun := by fun_prop }
  let m := e.toHomeomorph.toMeasurableEquiv
  have h := isFundamentalDomain_stdDom (Γ.subgroupOf N) (Measure.haar.map e)
  have hp : MeasurePreserving m Measure.haar (Measure.haar.map e) := ⟨m.measurable, rfl⟩
  have h' : IsFundamentalDomain (Γ.subgroupOf N) (m ⁻¹' stdDom (Γ.subgroupOf N)) Measure.haar :=
    h.preimage_of_equiv hp.quasiMeasurePreserving
      (e := fun δ => ⟨e.symm δ, mul_mem (mul_mem (inv_mem hγ) δ.2) hγ⟩)
      ⟨fun a b hab => Subtype.ext (e.symm.injective (congrArg Subtype.val hab)),
        fun δ => ⟨⟨e δ, mul_mem (mul_mem hγ δ.2) (inv_mem hγ)⟩, Subtype.ext (e.symm_apply_apply _)⟩⟩
      fun δ n => (map_mul e _ _).trans (congrArg (· * e n) (e.apply_symm_apply _))
  rw [constTermOn_eq h hφ, constTermOn_eq h' hφ, ← hp.setIntegral_preimage_emb m.measurableEmbedding,
    measureReal_def, measureReal_def, hp.measure_preimage h.nullMeasurableSet]
  refine congrArg _ (integral_congr_ae (.of_forall fun n => ?_))
  change φ (γ * n * γ⁻¹ * (γ * x)) = φ (n * x)
  rw [mul_assoc, inv_mul_cancel_left, mul_assoc, hφ γ hγ]

namespace Cocompact

variable (hc : Cocompact Γ N)
include hc

omit [LocallyCompactSpace N] in

theorem integrableOn [μ.IsHaarMeasure] (h : IsFundamentalDomain (Γ.subgroupOf N) 𝓕 μ) (hφ : LeftInv Γ φ)
    (hφc : Continuous φ) (x : G) : IntegrableOn (fun n : N => φ (n * x)) 𝓕 μ :=
  let ⟨K, hK, hs⟩ := hc
  GlobalTheory.integrableOn_fundamentalDomain_of_cocompact N _ K hK hs μ inferInstance 𝓕 h _ (by fun_prop)
    (leftInv_integrand hφ x)

omit [LocallyCompactSpace N] in

theorem measure_ne_top [μ.IsHaarMeasure] (h : IsFundamentalDomain (Γ.subgroupOf N) 𝓕 μ) : μ 𝓕 ≠ ⊤ :=
  ((integrableOn_const_iff (C := (1 : ℂ))).1
    (hc.integrableOn h (φ := fun _ => 1) (fun _ _ _ => rfl) continuous_const 1)).elim (by simp) LT.lt.ne

theorem isProbabilityMeasure : IsProbabilityMeasure (probMeasure Γ N) :=
  ⟨ENNReal.inv_mul_cancel (NeZero.ne _) (by
    rw [quotMeasure_univ (isFundamentalDomain_stdDom _ _)]; exact hc.measure_ne_top (isFundamentalDomain_stdDom _ _))⟩

theorem integrable (hφ : LeftInv Γ φ) (hφc : Continuous φ) (x : G) :
    Integrable (fun q : Quot (Γ.subgroupOf N) => φ ((q.out : N) * x)) (probMeasure Γ N) := by
  have h := isFundamentalDomain_stdDom (Γ.subgroupOf N) Measure.haar
  refine Integrable.smul_measure (memLp_one_iff_integrable.1 ((memLp_quotMeasure_iff h).2 ?_))
    (ENNReal.inv_ne_top.2 (NeZero.ne _))
  rw [show lift _ (fun q : Quot (Γ.subgroupOf N) => φ ((q.out : N) * x)) = _ from
    (leftInv_integrand (N := N) hφ x).lift_descend]
  exact memLp_one_iff_integrable.2 (hc.integrableOn h hφ hφc x)

theorem constTermOn_const (c : ℂ) (x : G) : constTermOn Γ N (fun _ => c) x = c := by
  have := hc.isProbabilityMeasure
  simp [constTermOn]

theorem constTermOn_add (hφ : LeftInv Γ φ) (hφc : Continuous φ) (hψ : LeftInv Γ ψ) (hψc : Continuous ψ) (x : G) :
    constTermOn Γ N (φ + ψ) x = constTermOn Γ N φ x + constTermOn Γ N ψ x :=
  integral_add (hc.integrable hφ hφc x) (hc.integrable hψ hψc x)

theorem constTermOn_eq_zero_iff [μ.IsHaarMeasure] (h : IsFundamentalDomain (Γ.subgroupOf N) 𝓕 μ) (hφ : LeftInv Γ φ)
    (x : G) : constTermOn Γ N φ x = 0 ↔ ∫ n in 𝓕, φ (n * x) ∂μ = 0 :=
  (constTermOn_eq h hφ x).symm ▸ smul_eq_zero_iff_right (inv_ne_zero
    (ENNReal.toReal_ne_zero.2 ⟨h.measure_ne_zero (NeZero.ne μ), hc.measure_ne_top h⟩))

theorem isMulRightInvariant (μ : Measure N) [μ.IsHaarMeasure] : μ.IsMulRightInvariant := ⟨fun g => by
  have h := isFundamentalDomain_stdDom (Γ.subgroupOf N) μ
  have e := Measure.isMulLeftInvariant_eq_smul (μ.map (· * g)) μ
  have h' : IsFundamentalDomain (Γ.subgroupOf N) ((· * g) ⁻¹' stdDom (Γ.subgroupOf N)) μ :=
    h.preimage_of_equiv ⟨measurable_mul_const g, e ▸ Measure.smul_absolutelyContinuous⟩ Function.bijective_id
      fun γ x => mul_assoc _ _ _
  have h1 := h'.measure_eq h
  rw [← Measure.map_apply (measurable_mul_const g) (measurableSet_stdDom _), e, Measure.smul_apply, ENNReal.smul_def,
    smul_eq_mul, ENNReal.mul_eq_right (h.measure_ne_zero (NeZero.ne μ)) (hc.measure_ne_top h), ENNReal.coe_eq_one] at h1
  rw [e, h1, one_smul]⟩

theorem constTermOn_mul_left (hφ : LeftInv Γ φ) {n : G} (hn : n ∈ N) (x : G) :
    constTermOn Γ N φ (n * x) = constTermOn Γ N φ x := by
  have := hc.isMulRightInvariant Measure.haar
  have h := isFundamentalDomain_stdDom (Γ.subgroupOf N) Measure.haar
  have hp := measurePreserving_mul_right (Measure.haar : Measure N) ⟨n, hn⟩
  have h' := h.preimage_of_equiv hp.quasiMeasurePreserving Function.bijective_id fun γ x => mul_assoc _ _ _
  rw [constTermOn_eq h' hφ, constTermOn_eq h hφ, ← hp.setIntegral_preimage_emb (measurableEmbedding_mulRight _) _
    (stdDom _), measureReal_def, measureReal_def, hp.measure_preimage h.nullMeasurableSet]
  simp only [Subgroup.coe_mul, mul_assoc]

theorem continuous_constTermOn [LocallyCompactSpace G] (hφ : LeftInv Γ φ) (hφc : Continuous φ) :
    Continuous (constTermOn Γ N φ) := by
  have := hc.isProbabilityMeasure
  obtain ⟨K, hK, hs⟩ := id hc
  refine continuous_iff_continuousAt.2 fun x => ?_
  obtain ⟨U, hU, hx⟩ := exists_compact_mem_nhds x
  obtain ⟨C, hC⟩ := (hK.prod hU).exists_bound_of_continuousOn (f := fun p : N × G => φ (p.1 * p.2)) (by fun_prop)
  refine continuousAt_of_dominated (bound := fun _ => C) (.of_forall fun y => (hc.integrable hφ hφc y).1)
    (Filter.Eventually.mono hx fun y hy => .of_forall fun q => ?_) (integrable_const C) (.of_forall fun q => by fun_prop)
  obtain ⟨γ, hγ, hk⟩ := hs q.out
  exact (congrArg norm (leftInv_integrand hφ y γ hγ q.out)).ge.trans (hC (_, y) ⟨hk, hy⟩)

end Cocompact

end GlobalTheory.Cusp

end
