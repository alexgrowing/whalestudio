import Mathlib
open MeasureTheory

namespace GlobalTheory

open Set Topology

theorem leftHaar_semidirect_coords : ∀ (G M : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [T2Space G]
    [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G] [Group M] [TopologicalSpace M] [IsTopologicalGroup M]
    [LocallyCompactSpace M] [T2Space M] [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M] (Q N : Subgroup G),
    IsClosed (Q : Set G) → IsClosed (N : Set G) → N ≤ Q → (∀ q ∈ Q, ∀ u ∈ N, q * u * q⁻¹ ∈ N) → ∀ m : M →* G, Continuous m →
    (∀ x, m x ∈ Q) → (∀ q ∈ Q, ∃! z : N × M, q = z.1.1 * m z.2) → ∀ (μN : Measure N) (μM : Measure M) [μN.IsHaarMeasure]
    [μM.IsHaarMeasure] (d : M → ENNReal), Continuous d → (∀ x y, d (x * y) = d x * d y) → (∀ x, d x ≠ 0 ∧ d x ≠ ⊤) →
    (∀ x (f : G → ENNReal), Measurable f → ∫⁻ u, f (m x * u.1 * (m x)⁻¹) ∂μN = d x * ∫⁻ u, f u.1 ∂μN) →
    ∃ ν : Measure Q, ν.IsHaarMeasure ∧ ∀ φ : G → ENNReal, Measurable φ → ∫⁻ q, φ q.1 ∂ν = ∫⁻ x, ∫⁻ u, φ (u.1 * m x) * d x ∂μN ∂μM := by
  intro G M _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Q N hQ hN hNQ hnorm m hm hmQ huniq μN μM _ _ d hd hmul hd0 hconj
  haveI : LocallyCompactSpace N := hN.isClosedEmbedding_subtypeVal.locallyCompactSpace
  haveI : SecondCountableTopology N := TopologicalSpace.Subtype.secondCountableTopology _
  haveI : SecondCountableTopology Q := TopologicalSpace.Subtype.secondCountableTopology _
  haveI : SigmaCompactSpace N := sigmaCompactSpace_of_locallyCompact_secondCountable
  haveI : LocallyCompactSpace Q := hQ.isClosedEmbedding_subtypeVal.locallyCompactSpace
  let Ψ : M × N → Q := fun z => ⟨z.2.1 * m z.1, Q.mul_mem (hNQ z.2.2) (hmQ z.1)⟩
  have hΨc : Continuous Ψ :=
    ((continuous_subtype_val.comp continuous_snd).mul (hm.comp continuous_fst)).subtype_mk _
  have hΨm : Measurable Ψ := hΨc.measurable
  have hinj : Function.Injective Ψ := by
    rintro ⟨x, u⟩ ⟨x', u'⟩ h
    have h1 : (Ψ (x, u)).1 = (Ψ (x', u')).1 := congrArg Subtype.val h
    obtain ⟨z, -, hz⟩ := huniq (Ψ (x, u)).1 (Ψ (x, u)).2
    have e1 := hz (u, x) rfl
    have e2 := hz (u', x') h1
    rw [← e1] at e2
    simp only [Prod.mk.injEq] at e2
    rw [e2.1, e2.2]
  have hsurj : Function.Surjective Ψ := by
    intro q
    obtain ⟨z, hz, -⟩ := huniq q.1 q.2
    exact ⟨(z.2, z.1), Subtype.ext hz.symm⟩
  have hfun : μM.withDensity d = μM.withDensity (fun x => ((d x).toNNReal : ENNReal)) := by
    congr 1; funext x; exact (ENNReal.coe_toNNReal (hd0 x).2).symm
  have hcN : Continuous fun x => (d x).toNNReal :=
    ENNReal.continuousOn_toNNReal.comp_continuous hd (fun x => (hd0 x).2)
  haveI : IsFiniteMeasureOnCompacts (μM.withDensity d) := by
    haveI := IsLocallyFiniteMeasure.withDensity_coe (μ := μM) hcN
    rw [hfun]; infer_instance
  let P : Measure (M × N) := (μM.withDensity d).prod μN
  let ν : Measure Q := P.map Ψ
  have formula : ∀ φ : G → ENNReal, Measurable φ →
      ∫⁻ q, φ q.1 ∂ν = ∫⁻ x, ∫⁻ u, φ (u.1 * m x) * d x ∂μN ∂μM := by
    intro φ hφ
    have hF : Measurable fun z : M × N => φ (Ψ z).1 := hφ.comp (continuous_subtype_val.comp hΨc).measurable
    rw [show (∫⁻ q, φ q.1 ∂ν) = ∫⁻ z, φ (Ψ z).1 ∂P from
        lintegral_map (f := fun q : Q => φ q.1) (hφ.comp measurable_subtype_coe) hΨm,
      lintegral_prod _ hF.aemeasurable,
      lintegral_withDensity_eq_lintegral_mul _ hd.measurable hF.lintegral_prod_right']
    congr 1; funext x
    simp only [Pi.mul_apply]
    rw [lintegral_mul_const' _ _ (hd0 x).2, mul_comm]
  have key : ∀ g : Q, ∀ φ : G → ENNReal, Measurable φ →
      ∫⁻ x, ∫⁻ u, φ (g.1 * (u.1 * m x)) * d x ∂μN ∂μM = ∫⁻ x, ∫⁻ u, φ (u.1 * m x) * d x ∂μN ∂μM := by
    intro g φ hφ
    obtain ⟨⟨u₀, x₀⟩, hg, -⟩ := huniq g.1 g.2
    simp only at hg
    let J : M → ENNReal := fun y => ∫⁻ u, φ (u.1 * m y) ∂μN
    have h1 : ∀ x, ∫⁻ u, φ (g.1 * (u.1 * m x)) * d x ∂μN = d x₀ * J (x₀ * x) * d x := by
      intro x
      rw [lintegral_mul_const' _ _ (hd0 x).2]
      congr 1
      have hc := hconj x₀ (fun y => φ (u₀.1 * y * m (x₀ * x)))
        (hφ.comp ((measurable_const_mul _).mul_const _))
      have e : ∀ u : N, g.1 * (u.1 * m x) = u₀.1 * (m x₀ * u.1 * (m x₀)⁻¹) * m (x₀ * x) := by
        intro u; rw [hg, map_mul]; group
      calc ∫⁻ u, φ (g.1 * (u.1 * m x)) ∂μN
          = ∫⁻ u, φ (u₀.1 * (m x₀ * u.1 * (m x₀)⁻¹) * m (x₀ * x)) ∂μN := by
            congr 1; funext u; rw [e]
        _ = d x₀ * ∫⁻ u, φ (u₀.1 * u.1 * m (x₀ * x)) ∂μN := hc
        _ = d x₀ * J (x₀ * x) := by
            congr 1
            exact lintegral_mul_left_eq_self (fun u : N => φ (u.1 * m (x₀ * x))) u₀
    calc ∫⁻ x, ∫⁻ u, φ (g.1 * (u.1 * m x)) * d x ∂μN ∂μM
        = ∫⁻ x, d x₀ * J (x₀ * x) * d x ∂μM := lintegral_congr h1
      _ = ∫⁻ x, J (x₀ * x) * d (x₀ * x) ∂μM := by
          congr 1; funext x; rw [hmul]; ring
      _ = ∫⁻ x, J x * d x ∂μM := lintegral_mul_left_eq_self (fun y => J y * d y) x₀
      _ = ∫⁻ x, ∫⁻ u, φ (u.1 * m x) * d x ∂μN ∂μM := by
          congr 1; funext x; rw [lintegral_mul_const' _ _ (hd0 x).2]
  have hset : ∀ T : Set G, MeasurableSet T →
      ν (Subtype.val ⁻¹' T) = ∫⁻ x, ∫⁻ u, T.indicator 1 (u.1 * m x) * d x ∂μN ∂μM := by
    intro T hT
    rw [← formula _ (measurable_one.indicator hT),
      ← lintegral_indicator_one (measurable_subtype_coe hT)]
    congr 1
  have hinv : ν.IsMulLeftInvariant := by
    refine ⟨fun g => ?_⟩
    ext S hS
    rw [Measure.map_apply (measurable_const_mul g) hS]
    obtain ⟨T, hT, rfl⟩ := hS
    have hpre : (fun q : Q => g * q) ⁻¹' (Subtype.val ⁻¹' T) =
        Subtype.val ⁻¹' ((fun y => g.1 * y) ⁻¹' T) := rfl
    rw [hpre, hset _ (measurable_const_mul _ hT), hset _ hT]
    have := key g (T.indicator 1) (measurable_one.indicator hT)
    rw [← this]
    congr 1
  refine ⟨ν, ?_, formula⟩
  let C : ℕ → Set (M × N) := compactCovering (M × N)
  have hCc : ∀ n, IsCompact (C n) := isCompact_compactCovering (M × N)
  have hclosed : ∀ n, IsClosed (Ψ '' C n) := fun n => ((hCc n).image hΨc).isClosed
  have hcov : ⋃ n, Ψ '' C n = univ := by
    rw [← image_iUnion, iUnion_compactCovering, image_univ_of_surjective hsurj]
  obtain ⟨n, hn⟩ := nonempty_interior_of_iUnion_of_closed hclosed hcov
  have hdens : (μM.withDensity d) univ ≠ 0 := by
    rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ, Ne,
      lintegral_eq_zero_iff hd.measurable]
    intro h
    have h2 : μM {x | ¬ d x = (0 : M → ENNReal) x} = 0 := ae_iff.1 h
    have h3 : {x | ¬ d x = (0 : M → ENNReal) x} = univ := by
      ext x; simp [(hd0 x).1]
    rw [h3] at h2
    exact isOpen_univ.measure_ne_zero μM univ_nonempty h2
  have hP0 : P univ ≠ 0 := by
    rw [← univ_prod_univ, Measure.prod_prod]
    exact mul_ne_zero hdens (isOpen_univ.measure_ne_zero μN univ_nonempty)
  obtain ⟨k, hk⟩ : ∃ k, P (C k) ≠ 0 := by
    by_contra h
    push_neg at h
    apply hP0
    rw [← iUnion_compactCovering (M × N)]
    exact measure_iUnion_null h
  have hK : IsCompact (Ψ '' C (max n k)) := (hCc _).image hΨc
  refine Measure.isHaarMeasure_of_isCompact_nonempty_interior ν _ hK
    (hn.mono (interior_mono (image_mono (compactCovering_subset _ (le_max_left n k))))) ?_ ?_
  · rw [Measure.map_apply hΨm hK.isClosed.measurableSet]
    intro h0
    exact hk (measure_mono_null
      ((compactCovering_subset _ (le_max_right n k)).trans (subset_preimage_image Ψ _)) h0)
  · rw [Measure.map_apply hΨm hK.isClosed.measurableSet, preimage_image_eq _ hinj]
    exact (hCc _).measure_lt_top.ne

end GlobalTheory
