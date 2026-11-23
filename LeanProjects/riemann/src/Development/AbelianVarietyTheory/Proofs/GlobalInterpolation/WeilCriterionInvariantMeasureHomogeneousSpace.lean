import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.InvariantRadonFibre
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsBruhatFunctionClosedSubgroup
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsUniqueHaarOfInvariantRadonOnCosets

open MeasureTheory MeasureTheory.Measure GlobalTheory.IndefiniteRowSideFullHecke.InvariantRadonFibre Topology
open scoped ENNReal NNReal

namespace GlobalTheory.WeilCriterion

section Modulus

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G]

theorem lintegral_mul_right_eq_modulus (μ : Measure G) [μ.IsHaarMeasure] {f : G → ℝ≥0∞}
    (hf : Measurable f) (g : G) :
    ∫⁻ x, f (x * g) ∂μ = (modularCharacterFun g : ℝ≥0∞) * ∫⁻ x, f x ∂μ := by
  rw [← lintegral_map hf (measurable_mul_const g), map_right_mul_eq_modularCharacterFun_smul,
    lintegral_smul_measure]
  rfl

theorem measure_preimage_mul_right_eq_modulus (μ : Measure G) [μ.IsHaarMeasure] {s : Set G}
    (hs : MeasurableSet s) (g : G) :
    μ ((· * g) ⁻¹' s) = (modularCharacterFun g : ℝ≥0∞) * μ s := by
  rw [← Measure.map_apply (measurable_mul_const g) hs, map_right_mul_eq_modularCharacterFun_smul]
  rfl

theorem exists_measurableSet_pos_finite (μ : Measure G) [μ.IsHaarMeasure] :
    ∃ s : Set G, MeasurableSet s ∧ μ s ≠ 0 ∧ μ s ≠ ⊤ := by
  obtain ⟨K, hK, hK1⟩ := exists_compact_mem_nhds (1 : G)
  exact ⟨K, hK.measurableSet, (measure_pos_of_mem_nhds μ hK1).ne', hK.measure_lt_top.ne⟩

theorem measurable_modulus : Measurable fun g : G => (modularCharacterFun g : ℝ≥0∞) := by
  let μ : Measure G := haar
  obtain ⟨s, hs, h0, ht⟩ := exists_measurableSet_pos_finite μ
  have h : (fun g : G => (modularCharacterFun g : ℝ≥0∞)) =
      fun g => μ ((· * g) ⁻¹' s) * (μ s)⁻¹ := by
    funext g
    rw [measure_preimage_mul_right_eq_modulus μ hs, mul_assoc, ENNReal.mul_inv_cancel h0 ht,
      mul_one]
  rw [h]
  exact (measurable_measure_mul_right μ hs).mul_const _

theorem lintegral_modulus_mul_inv (μ : Measure G) [μ.IsHaarMeasure] {f : G → ℝ≥0∞}
    (hf : Measurable f) :
    ∫⁻ x, (modularCharacterFun x : ℝ≥0∞) * f x⁻¹ ∂μ = ∫⁻ x, f x ∂μ := by
  obtain ⟨s, hs, h0, ht⟩ := exists_measurableSet_pos_finite μ
  have h := measure_mul_lintegral_eq μ μ hs f hf
  simp_rw [measure_preimage_mul_right_eq_modulus μ hs] at h
  have h2 : ∫⁻ x, (modularCharacterFun x : ℝ≥0∞) * μ s * f x⁻¹ ∂μ =
      μ s * ∫⁻ x, (modularCharacterFun x : ℝ≥0∞) * f x⁻¹ ∂μ := by
    rw [← lintegral_const_mul' _ _ ht]
    congr 1
    funext x
    ring
  rw [h2] at h
  exact ((ENNReal.mul_right_inj h0 ht).mp h).symm

end Modulus

section Main

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
  (H : Subgroup G) [LocallyCompactSpace H]

theorem lintegral_mul_fibre_symm
    (hΔ : ∀ h : H, modularCharacterFun (h : G) = modularCharacterFun h)
    (dg : Measure G) [dg.IsHaarMeasure] (ν : Measure H) [ν.IsHaarMeasure]
    {f f' : G → ℝ≥0∞} (hf : Measurable f) (hf' : Measurable f') :
    ∫⁻ g, f g * ∫⁻ h : H, f' (g * h) ∂ν ∂dg = ∫⁻ g, (∫⁻ h : H, f (g * h) ∂ν) * f' g ∂dg := by
  haveI : SecondCountableTopology H := TopologicalSpace.Subtype.secondCountableTopology _
  have e1 : ∀ g, f g * ∫⁻ h : H, f' (g * h) ∂ν = ∫⁻ h : H, f g * f' (g * h) ∂ν := fun g =>
    (lintegral_const_mul _ (by fun_prop)).symm
  have e2 : ∀ g, (∫⁻ h : H, f (g * h) ∂ν) * f' g =
      ∫⁻ h : H, (modularCharacterFun h : ℝ≥0∞) * (f (g * (h : G)⁻¹) * f' g) ∂ν := fun g => by
    rw [← lintegral_mul_const _ (by fun_prop),
      ← lintegral_modulus_mul_inv ν (f := fun h : H => f (g * h) * f' g) (by fun_prop)]
    rfl
  have hm := measurable_modulus (G := H)
  simp_rw [e1, e2]
  have m1 : Measurable fun p : G × H => f p.1 * f' (p.1 * p.2) := by fun_prop
  have m2 : Measurable fun p : G × H => f (p.1 * (p.2 : G)⁻¹) * f' p.1 := by fun_prop
  rw [lintegral_lintegral_swap m1.aemeasurable,
    lintegral_lintegral_swap (μ := dg) ((hm.comp measurable_snd).mul m2).aemeasurable]
  congr 1
  funext h
  rw [lintegral_const_mul _ (by fun_prop), ← hΔ,
    ← lintegral_mul_right_eq_modulus dg (f := fun g => f (g * (h : G)⁻¹) * f' g) (by fun_prop)]
  simp

variable [MeasurableSpace (G ⧸ H)] [BorelSpace (G ⧸ H)]

omit [LocallyCompactSpace G] [SecondCountableTopology G] [T2Space G] [LocallyCompactSpace H]
  [IsTopologicalGroup G] in
theorem measurable_mk : Measurable (QuotientGroup.mk : G → G ⧸ H) :=
  QuotientGroup.continuous_mk.measurable

omit [LocallyCompactSpace G] [T2Space G] [LocallyCompactSpace H] [SecondCountableTopology G] in

theorem fibre_comp_mk_mul (ν : Measure H) {φ : G → ℝ≥0∞} (hφ : Measurable φ)
    (hφ1 : ∀ g : G, ∫⁻ h : H, φ (g * h) ∂ν = 1) (F : G ⧸ H → ℝ≥0∞) (g : G) :
    ∫⁻ h : H, F ((g * h : G) : G ⧸ H) * φ (g * h) ∂ν = F (g : G ⧸ H) := by
  simp_rw [QuotientGroup.mk_mul_of_mem g (Subtype.property _)]
  rw [lintegral_const_mul _ (by fun_prop), hφ1, mul_one]

theorem lintegral_comp_mk_mul_indep
    (hΔ : ∀ h : H, modularCharacterFun (h : G) = modularCharacterFun h)
    (dg : Measure G) [dg.IsHaarMeasure] (ν : Measure H) [ν.IsHaarMeasure]
    {φ ψ : G → ℝ≥0∞} (hφ : Measurable φ) (hφ1 : ∀ g : G, ∫⁻ h : H, φ (g * h) ∂ν = 1)
    (hψ : Measurable ψ) (hψ1 : ∀ g : G, ∫⁻ h : H, ψ (g * h) ∂ν = 1)
    {F : G ⧸ H → ℝ≥0∞} (hF : Measurable F) :
    ∫⁻ g, F (g : G ⧸ H) * φ g ∂dg = ∫⁻ g, F (g : G ⧸ H) * ψ g ∂dg := by
  have h := lintegral_mul_fibre_symm H hΔ dg ν (f := fun g => F (g : G ⧸ H) * φ g)
    ((hF.comp (measurable_mk H)).mul hφ) hψ
  simp_rw [hψ1, mul_one, fibre_comp_mk_mul H ν hφ hφ1] at h
  exact h

omit [LocallyCompactSpace G] [SecondCountableTopology G] [T2Space G] [LocallyCompactSpace H]
  [IsTopologicalGroup G] in
theorem map_withDensity_apply (dg : Measure G) {φ : G → ℝ≥0∞} (hφ : Measurable φ)
    {A : Set (G ⧸ H)} (hA : MeasurableSet A) :
    (dg.withDensity φ).map (QuotientGroup.mk : G → G ⧸ H) A =
      ∫⁻ g, A.indicator 1 (g : G ⧸ H) * φ g ∂dg := by
  rw [← lintegral_indicator_one hA,
    lintegral_map (measurable_one.indicator hA) (measurable_mk H),
    lintegral_withDensity_eq_lintegral_mul _ hφ (g := fun g : G => A.indicator 1 (g : G ⧸ H))
      ((measurable_one.indicator hA).comp (measurable_mk H))]
  simp [mul_comm]

theorem exists_isInvariantRadon (hH : IsClosed (H : Set G))
    (hΔ : ∀ h : H, modularCharacterFun (h : G) = modularCharacterFun h) :
    ∃ μ : Measure (G ⧸ H), IsInvariantRadon H μ := by
  let dg : Measure G := haar
  let ν : Measure H := haar
  obtain ⟨φ, hφ, hφ1, hφK⟩ := GlobalTheory.exists_bruhat_function_closed_subgroup G H hH ν
  refine ⟨(dg.withDensity φ).map (QuotientGroup.mk : G → G ⧸ H), ?_, ⟨fun K hK => ?_⟩,
    ⟨fun a A hA => ?_⟩⟩
  · intro h0
    have h1 := map_withDensity_apply H dg hφ MeasurableSet.univ
    rw [h0] at h1
    simp only [Measure.coe_zero, Pi.zero_apply, Set.indicator_univ, Pi.one_apply, one_mul] at h1
    have h2 : φ =ᵐ[dg] 0 := (lintegral_eq_zero_iff hφ).mp h1.symm
    have h3 := lintegral_mul_fibre_symm H hΔ dg ν (f := fun _ => 1) measurable_const hφ
    simp_rw [hφ1] at h3
    have h4 : ∫⁻ g, (∫⁻ h : H, (1 : ℝ≥0∞) ∂ν) * φ g ∂dg = 0 := by
      rw [lintegral_const_mul _ hφ, ← h1, mul_zero]
    rw [h4] at h3
    simp only [mul_one, lintegral_const, one_mul, measure_univ_eq_zero] at h3
    exact NeZero.ne dg h3
  · refine hK.measure_lt_top_of_nhdsWithin fun q _ => ?_
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
    obtain ⟨K₀, hK₀, hg⟩ := exists_compact_mem_nhds g
    obtain ⟨K', C, hK', hC, hb⟩ := hφK K₀ hK₀
    have hc : IsCompact ((QuotientGroup.mk : G → G ⧸ H) '' K₀) :=
      hK₀.image QuotientGroup.continuous_mk
    haveI : IsClosed (H : Set G) := hH
    refine ⟨(QuotientGroup.mk : G → G ⧸ H) '' K₀,
      mem_nhdsWithin_of_mem_nhds (QuotientGroup.isOpenMap_coe.image_mem_nhds hg), ?_⟩
    rw [map_withDensity_apply H dg hφ hc.measurableSet]
    calc _ ≤ ∫⁻ x, K'.indicator (fun _ => C) x ∂dg := by
          refine lintegral_mono fun x => ?_
          by_cases hx : (x : G ⧸ H) ∈ (QuotientGroup.mk : G → G ⧸ H) '' K₀
          · obtain ⟨k, hk, hkx⟩ := hx
            have hmem : k⁻¹ * x ∈ H := QuotientGroup.eq.mp hkx
            have h := hb k hk ⟨_, hmem⟩
            simp only [mul_inv_cancel_left] at h
            by_cases h0 : φ x = 0
            · simp [h0]
            · rw [Set.indicator_of_mem (h.2 h0), Set.indicator_of_mem (Set.mem_image_of_mem _ hk |> (hkx ▸ ·))]
              simpa using h.1
          · simp [Set.indicator_of_notMem hx]
      _ = C * dg K' := lintegral_indicator_const hK'.measurableSet C
      _ < ⊤ := ENNReal.mul_lt_top hC hK'.measure_lt_top
  · have hA' : MeasurableSet ((fun x : G ⧸ H => a • x) ⁻¹' A) :=
      (continuous_const_smul a).measurable hA
    rw [map_withDensity_apply H dg hφ hA', map_withDensity_apply H dg hφ hA,
      lintegral_comp_mk_mul_indep H hΔ dg ν hφ hφ1 (ψ := fun g => φ (a * g)) (by fun_prop)
        (fun g => by simpa [mul_assoc] using hφ1 (a * g)) (measurable_one.indicator hA'),
      ← lintegral_mul_left_eq_self (fun g : G => A.indicator 1 (g : G ⧸ H) * φ g) a]
    rfl

theorem isInvariantRadon_unique (hH : IsClosed (H : Set G)) (μ μ' : Measure (G ⧸ H))
    (hμ : IsInvariantRadon H μ) (hμ' : IsInvariantRadon H μ') :
    ∃ c : ℝ≥0, 0 < c ∧ μ' = c • μ := by
  let ν : Measure H := haar
  obtain ⟨φ, hφ, hφ1, -⟩ := GlobalTheory.exists_bruhat_function_closed_subgroup G H hH ν
  obtain ⟨dg, ⟨hdg, hq⟩, -⟩ := GlobalTheory.QuotientHaar.existsUnique_haar_of_invariantRadon G H hH ν μ hμ
  obtain ⟨dg', ⟨hdg', hq'⟩, -⟩ := GlobalTheory.QuotientHaar.existsUnique_haar_of_invariantRadon G H hH ν μ' hμ'
  refine ⟨haarScalarFactor dg' dg, haarScalarFactor_pos_of_isHaarMeasure _ _, ?_⟩
  ext A hA
  have hm : Measurable fun g : G => A.indicator (1 : G ⧸ H → ℝ≥0∞) (g : G ⧸ H) * φ g :=
    ((measurable_one.indicator hA).comp (measurable_mk H)).mul hφ
  have hfib : fibreIntegral H ν (fun g : G => A.indicator (1 : G ⧸ H → ℝ≥0∞) (g : G ⧸ H) * φ g) =
      A.indicator 1 := by
    funext q
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
    rw [fibreIntegral_mk]
    exact fibre_comp_mk_mul H ν hφ hφ1 _ g
  have h1 := (hq _ hm).2
  have h2 := (hq' _ hm).2
  rw [hfib, lintegral_indicator_one hA] at h1 h2
  rw [Measure.smul_apply, ← h1, ← h2]
  conv_lhs => rw [isMulLeftInvariant_eq_smul dg' dg]
  rw [lintegral_smul_measure]

end Main

theorem modulusClause : ModulusClause := by
  intro G _ _ _ _ _ _ H _ _ _ hH hΔ
  borelize G
  exact ⟨exists_isInvariantRadon H hH hΔ, isInvariantRadon_unique H hH⟩

end GlobalTheory.WeilCriterion
