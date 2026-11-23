import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HaarMeasureIwasawaQuotient
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPositiveAveragingFunctionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IwasawaAveragingIntegralFormulaStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IwasawaQuotientIntegralFormulaStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuotientIntegralEquivariantComplexStatement
open MeasureTheory
open scoped NNReal ENNReal

noncomputable section
namespace GlobalTheory.IwasawaAbs

theorem modulus_facts {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
    [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G] (P K : Subgroup G)
    (μP : Measure P) [μP.IsHaarMeasure] (δ : P → ℝ≥0) (hP : IsClosed (P : Set G)) (hK : IsCompact (K : Set G))
    (hδ : ∀ p : P, μP.map (· * p) = δ p • μP) :
    (∀ p : P, δ p ≠ 0) ∧ ∀ p : P, (p : G) ∈ K → δ p = 1 := by
  haveI : LocallyCompactSpace P := hP.isClosedEmbedding_subtypeVal.locallyCompactSpace
  haveI : SecondCountableTopology P := TopologicalSpace.Subtype.secondCountableTopology _
  obtain ⟨A, hA, hA1⟩ := exists_compact_mem_nhds (1 : P)
  have hpos : μP A ≠ 0 := (Measure.measure_pos_of_mem_nhds μP hA1).ne'
  have hfin : μP A ≠ ∞ := hA.measure_lt_top.ne
  refine ⟨fun p h0 => ?_, fun p hp => ?_⟩
  · have h := hδ p
    rw [h0, zero_smul] at h
    have h2 := congrArg (fun m : Measure P => m Set.univ) h
    simp only [Measure.map_apply (measurable_mul_const p) MeasurableSet.univ, Set.preimage_univ,
      Measure.coe_zero, Pi.zero_apply] at h2
    exact hpos (measure_mono_null (Set.subset_univ A) h2)
  · have hKP : IsCompact ((K.subgroupOf P : Subgroup P) : Set P) := by
      rw [Subgroup.coe_subgroupOf]
      exact hP.isClosedEmbedding_subtypeVal.isCompact_preimage hK
    have h1 := GlobalTheory.NAK.map_mul_right_eq_of_mem_compact μP (K.subgroupOf P) hKP p
      (by simpa [Subgroup.mem_subgroupOf] using hp)
    rw [hδ p] at h1
    have h2 := congrArg (fun m : Measure P => m A) h1
    simp only [Measure.coe_nnreal_smul_apply] at h2
    have h3 : (δ p : ℝ≥0∞) * μP A = 1 * μP A := by rw [one_mul]; exact h2
    exact_mod_cast (ENNReal.mul_left_inj hpos hfin).1 h3

theorem kIntegral_mul_right_eq : ∀ (G Kt : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
    [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G] [Group Kt] [TopologicalSpace Kt]
    [IsTopologicalGroup Kt] [CompactSpace Kt] [T2Space Kt] [MeasurableSpace Kt] [BorelSpace Kt]
    (ι : Kt →* G) (P : Subgroup G) (μG : Measure G) (μP : Measure P) (μK : Measure Kt) (δ : P → ℝ≥0),
    Continuous ι → Function.Injective ι → IsClosed (P : Set G) → μG.IsHaarMeasure → μP.IsHaarMeasure →
    μK.IsHaarMeasure → (∀ h : G, μG.map (· * h) = μG) → (∀ p : P, μP.map (· * p) = δ p • μP) →
    (∀ g : G, ∃ p ∈ P, ∃ k : Kt, g = p * ι k) → ∀ Ψ : G → ℂ,
    (∀ g : G, Integrable (fun k => Ψ (ι k * g)) μK) → (∀ (p : P) (g : G), Ψ (p * g) = (δ p : ℂ) * Ψ g) →
    ∀ g : G, ∫ k, Ψ (ι k * g) ∂μK = ∫ k, Ψ (ι k) ∂μK := by
  intro G Kt _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ι P μG μP μK δ hι hinj hP hG hPH hKH hright hδ hdec Ψ hint heq g
  set K : Subgroup G := ι.range with hKdef
  have hKc : IsCompact (K : Set G) := by rw [hKdef, MonoidHom.coe_range]; exact isCompact_range hι
  let r : Kt →* K := ι.rangeRestrict
  have hr : Continuous r := continuous_induced_rng.2 hι
  have hrinj : Function.Injective r := MonoidHom.rangeRestrict_injective_iff.2 hinj
  have hrsurj : Function.Surjective r := MonoidHom.rangeRestrict_surjective ι
  let e : Kt ≃ₜ K := hr.homeoOfEquivCompactToT2 (f := Equiv.ofBijective r ⟨hrinj, hrsurj⟩)
  have he : MeasurableEmbedding (r : Kt → K) := e.measurableEmbedding
  set μK' : Measure K := μK.map r with hμK'
  haveI : μK'.IsHaarMeasure :=
    Measure.isHaarMeasure_map μK r hr hrsurj (by rw [Filter.cocompact_eq_bot]; exact Filter.tendsto_bot)
  have hdec' : ∀ g : G, ∃ p ∈ P, ∃ k ∈ K, g = p * k := fun g => by
    obtain ⟨p, hp, k, rfl⟩ := hdec g
    exact ⟨p, hp, ι k, ⟨k, rfl⟩, rfl⟩
  have core : ∀ Φ : G → ℝ≥0∞, (∀ (p : P) (g : G), Φ ((p : G) * g) = (δ p : ℝ≥0∞) * Φ g) →
      (∀ g : G, AEMeasurable (fun x : K => Φ ((x : G) * g)) μK') → ∀ g : G,
      ∫⁻ x : K, Φ ((x : G) * g) ∂μK' = ∫⁻ x : K, Φ (x : G) ∂μK' := by
    intro Φ hΦ hae g
    haveI : LocallyCompactSpace P := hP.isClosedEmbedding_subtypeVal.locallyCompactSpace
    haveI : SecondCountableTopology P := TopologicalSpace.Subtype.secondCountableTopology _
    obtain ⟨b, hb, hbU⟩ := GlobalTheory.T.exists_positive_averaging_function G P K μP hP hKc hPH hdec'
    obtain ⟨hδ0, hδ1⟩ := modulus_facts P K μP δ hP hKc hδ
    set U : G → ℝ≥0∞ := fun g => ∫⁻ q : P, b ((q : G) * g) ∂μP with hUdef
    have hUm : Measurable U := by
      have : Measurable fun x : G × P => b ((x.2 : G) * x.1) :=
        hb.comp ((measurable_subtype_coe.comp measurable_snd).mul measurable_fst)
      exact this.lintegral_prod_right'
    have hUeq : ∀ (p : P) (g : G), U ((p : G) * g) = (δ p : ℝ≥0∞) * U g := by
      intro p g
      have hbg : Measurable fun q : P => b ((q : G) * g) := hb.comp (measurable_subtype_coe.mul_const g)
      calc U ((p : G) * g) = ∫⁻ q : P, (fun q' : P => b ((q' : G) * g)) (q * p) ∂μP := by
            simp only [hUdef, Subgroup.coe_mul, mul_assoc]
        _ = ∫⁻ q : P, b ((q : G) * g) ∂(μP.map (· * p)) := (lintegral_map hbg (measurable_mul_const p)).symm
        _ = (δ p : ℝ≥0∞) * U g := by rw [hδ p, lintegral_smul_measure, ENNReal.smul_def, smul_eq_mul]
    have hΦae : AEMeasurable Φ μG :=
      GlobalTheory.T.iwasawa_quotient_integral_formula G P K μG μP μK' δ U hP hKc hG hPH inferInstance hright hδ hdec' hUm hbU hUeq hδ1 Φ hΦ
        (by simpa using hae 1)
    exact GlobalTheory.T.iwasawa_averaging_integral_formula G P K μG μP μK' δ b hP hKc hG hPH inferInstance hright hδ hdec' hb hbU Φ hΦae hΦ g
  have key := GlobalTheory.T.quotient_integral_equivariant_complex G P K μK' (fun x => (x : G)) δ core
  have hint' : ∀ g : G, Integrable (fun x : K => Ψ ((x : G) * g)) μK' := fun g => by
    rw [hμK', he.integrable_map_iff]
    exact hint g
  have h := key Ψ hint' heq g
  rw [hμK', he.integral_map, he.integral_map] at h
  exact h

end GlobalTheory.IwasawaAbs
