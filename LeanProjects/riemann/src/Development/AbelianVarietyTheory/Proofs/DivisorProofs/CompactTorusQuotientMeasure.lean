import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoordMeasure
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.WeilIntegrationFormulaOrbit

open MeasureTheory
open scoped NNReal ENNReal

namespace GlobalTheory.TwoSidedInv

theorem map_haar_eq_smul {H X : Type} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
    [LocallyCompactSpace H] [T2Space H] [SecondCountableTopology H] [MeasurableSpace H] [BorelSpace H]
    [MulAction H X] [TopologicalSpace X] [T2Space X] [SecondCountableTopology X] [MeasurableSpace X]
    [BorelSpace X] (x0 : X) (hcont : Continuous (fun p : H × X => p.1 • p.2))
    (htr : ∀ y : X, ∃ h : H, h • x0 = y) (hS : IsCompact (MulAction.stabilizer H x0 : Set H))
    (μ : Measure H) [μ.IsHaarMeasure] (ν : Measure X) [IsFiniteMeasureOnCompacts ν]
    (hinv : ∀ (h : H) (s : Set X), MeasurableSet s → ν ((fun y => h • y) ⁻¹' s) = ν s) (hne : ν ≠ 0) :
    ∃ c : ℝ≥0∞, c ≠ 0 ∧ c ≠ ⊤ ∧ μ.map (fun h => h • x0) = c • ν := by
  have hc0 : Continuous (fun h : H => h • x0) := hcont.comp (continuous_id.prodMk continuous_const)
  obtain ⟨μ', hμ', hf⟩ := GlobalTheory.WeilOrbit.weil_formula H X x0 hcont μ inferInstance ν
    (by simp [htr]) hinv (fun K hK => (hK.image hc0).measure_lt_top) hne
  choose s hs using htr
  haveI : CompactSpace (MulAction.stabilizer H x0) := isCompact_iff_compactSpace.mp hS
  refine ⟨μ' Set.univ, (Measure.measure_univ_pos.mpr (NeZero.ne μ')).ne', measure_ne_top μ' _, ?_⟩
  ext A hA
  rw [Measure.map_apply hc0.measurable hA, Measure.smul_apply, smul_eq_mul]
  have hm : MeasurableSet ((fun h : H => h • x0) ⁻¹' A) := hA.preimage hc0.measurable
  have key := hf (((fun h : H => h • x0) ⁻¹' A).indicator 1) (measurable_one.indicator hm) s
    (fun y _ => hs y)
  rw [lintegral_indicator_one hm] at key
  rw [key]
  have hin : ∀ y, ∀ h' : MulAction.stabilizer H x0,
      ((fun h : H => h • x0) ⁻¹' A).indicator (1 : H → ℝ≥0∞) (s y * (h' : H)) = A.indicator 1 y := by
    intro y h'
    have : (s y * (h' : H)) • x0 = y := by
      rw [mul_smul, MulAction.mem_stabilizer_iff.mp h'.2, hs y]
    have hiff : s y * (h' : H) ∈ (fun h : H => h • x0) ⁻¹' A ↔ y ∈ A := by
      show (s y * (h' : H)) • x0 ∈ A ↔ y ∈ A
      rw [this]
    by_cases hy : y ∈ A
    · rw [Set.indicator_of_mem (hiff.2 hy), Set.indicator_of_mem hy]; rfl
    · rw [Set.indicator_of_notMem (fun h => hy (hiff.1 h)), Set.indicator_of_notMem hy]
  simp_rw [hin, lintegral_const]
  rw [lintegral_mul_const _ (measurable_one.indicator hA), lintegral_indicator_one hA, mul_comm]

theorem map_mul_right_compact {G K : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [LocallyCompactSpace G] [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G] [Group K]
    [TopologicalSpace K] [CompactSpace K] (κ : K →* G) (hκ : Continuous κ) (μ : Measure G) [μ.IsHaarMeasure] (k : K) :
    μ.map (fun x => x * κ k) = μ := by
  obtain ⟨C, hC, h1⟩ := exists_compact_mem_nhds (1 : G)
  set A : Set G := (fun p : G × K => p.1 * κ p.2) '' (C ×ˢ Set.univ) with hAdef
  have hAc : IsCompact A := (hC.prod isCompact_univ).image (by fun_prop)
  have hCA : C ⊆ A := fun x hx => ⟨(x, 1), ⟨hx, Set.mem_univ _⟩, by simp⟩
  have hpos : μ A ≠ 0 := (lt_of_lt_of_le (Measure.measure_pos_of_mem_nhds μ h1) (measure_mono hCA)).ne'
  have htop : μ A ≠ ⊤ := hAc.measure_lt_top.ne
  have hpre : (fun x => x * κ k) ⁻¹' A = A := by
    ext x
    simp only [hAdef, Set.mem_preimage, Set.mem_image, Set.mem_prod, Set.mem_univ, and_true, Prod.exists]
    constructor
    · rintro ⟨c, k', hc, he⟩
      refine ⟨c, k' * k⁻¹, hc, ?_⟩
      rw [map_mul, map_inv, ← mul_assoc, he, mul_inv_cancel_right]
    · rintro ⟨c, k', hc, he⟩
      exact ⟨c, k' * k, hc, by rw [map_mul, ← mul_assoc, he]⟩
  have hme := congrArg (fun ρ : Measure G => ρ A) (Measure.map_right_mul_eq_modularCharacterFun_smul μ (κ k))
  rw [Measure.map_apply (measurable_mul_const _) hAc.measurableSet, hpre] at hme
  have hΔ : Measure.modularCharacterFun (κ k) = 1 := by
    rw [Measure.smul_apply, ENNReal.smul_def, smul_eq_mul] at hme
    have h2 : (Measure.modularCharacterFun (κ k) : ℝ≥0∞) * μ A = 1 * μ A := by
      rw [one_mul]; exact hme.symm
    exact_mod_cast (ENNReal.mul_left_inj hpos htop).1 h2
  rw [Measure.map_right_mul_eq_modularCharacterFun_smul μ (κ k), hΔ, one_smul]

end GlobalTheory.TwoSidedInv

namespace GlobalTheory.TwoSidedInv

def parabolic {G T : Type} [Group G] [CommGroup T] (Q : Subgroup G) (m : T →* G)
    (hn : ∀ t, ∀ q ∈ Q, (m t)⁻¹ * q * m t ∈ Q) : Subgroup G where
  carrier := {x | ∃ q ∈ Q, ∃ t, x = q * m t}
  one_mem' := ⟨1, Q.one_mem, 1, by simp⟩
  mul_mem' := by
    rintro _ _ ⟨q, hq, t, rfl⟩ ⟨q', hq', t', rfl⟩
    refine ⟨q * (m t * q' * (m t)⁻¹), Q.mul_mem hq ?_, t * t', ?_⟩
    · have := hn t⁻¹ q' hq'
      simpa [map_inv] using this
    · simp [map_mul, mul_assoc]
  inv_mem' := by
    rintro _ ⟨q, hq, t, rfl⟩
    refine ⟨(m t)⁻¹ * q⁻¹ * m t, hn t _ (Q.inv_mem hq), t⁻¹, ?_⟩
    simp [map_inv, mul_assoc]

@[reducible] def twoSidedAction {G K : Type} [Group G] [Group K] (P : Subgroup G) (κ : K →* G) :
    MulAction (P × K) G where
  smul h x := (h.1 : G) * x * (κ h.2)⁻¹
  one_smul x := by
    show ((1 : P) : G) * x * (κ 1)⁻¹ = x
    simp
  mul_smul a b x := by
    show ((a.1 * b.1 : P) : G) * x * (κ (a.2 * b.2))⁻¹ = (a.1 : G) * ((b.1 : G) * x * (κ b.2)⁻¹) * (κ a.2)⁻¹
    simp only [Subgroup.coe_mul, map_mul, mul_inv_rev, mul_assoc]

theorem isMulLeftInvariant_of_parabolic : ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
    [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
    (K : Type) [Group K] [TopologicalSpace K] [IsTopologicalGroup K] [CompactSpace K] [SecondCountableTopology K]
    [T2Space K] [MeasurableSpace K] [BorelSpace K]
    (T : Type) [CommGroup T] [TopologicalSpace T] [IsTopologicalGroup T] [LocallyCompactSpace T] [SecondCountableTopology T]
    [T2Space T] [MeasurableSpace T] [BorelSpace T]
    (Q : Subgroup G) (κ : K →* G) (m : T →* G),
    IsClosed (Q : Set G) → Continuous κ → Topology.IsClosedEmbedding m →
    ∀ hn : (∀ t, ∀ q ∈ Q, (m t)⁻¹ * q * m t ∈ Q),
    (∀ t, m t ∈ Q → t = 1) →
    IsClosed {x : G | ∃ q ∈ Q, ∃ t, x = q * m t} →
    (∀ x : G, ∃ q ∈ Q, ∃ t k, x = q * (m t)⁻¹ * κ k) →
    ∀ ν : Measure G, IsFiniteMeasureOnCompacts ν → (∀ q ∈ Q, ν.map (fun x => q * x) = ν) →
    (∀ s, ν.map (fun x => m s * x) = ν) → (∀ k, ν.map (fun x => x * κ k) = ν) → ν.IsMulLeftInvariant := by
  intro G _ _ _ _ _ _ _ _ K _ _ _ _ _ _ _ _ T _ _ _ _ _ _ _ _ Q κ m hQ hκ hm hn hT hP hdec ν hνc hνQ hνm hνK
  set P := parabolic Q m hn with hPdef
  have hPc : IsClosed (P : Set G) := hP
  haveI : LocallyCompactSpace P := hPc.isClosedEmbedding_subtypeVal.locallyCompactSpace
  haveI : SecondCountableTopology P := TopologicalSpace.Subtype.secondCountableTopology _
  haveI : SecondCountableTopology (P × K) := inferInstance
  letI : MulAction (P × K) G := twoSidedAction P κ
  have hsmul : ∀ (h : P × K) (x : G), h • x = (h.1 : G) * x * (κ h.2)⁻¹ := fun _ _ => rfl
  have hcont : Continuous (fun p : (P × K) × G => p.1 • p.2) := by
    simp only [hsmul]
    fun_prop
  have htr : ∀ y : G, ∃ h : P × K, h • (1 : G) = y := by
    intro y
    obtain ⟨q, hq, t, k, rfl⟩ := hdec y
    exact ⟨(⟨q * m t⁻¹, q, hq, t⁻¹, rfl⟩, k⁻¹), by simp [hsmul, map_inv]⟩
  have hS : IsCompact (MulAction.stabilizer (P × K) (1 : G) : Set (P × K)) := by
    have hcl : IsClosed (MulAction.stabilizer (P × K) (1 : G) : Set (P × K)) :=
      isClosed_eq (hcont.comp (continuous_id.prodMk continuous_const)) continuous_const
    refine IsCompact.of_isClosed_subset
      ((hPc.isClosedEmbedding_subtypeVal.isCompact_preimage (isCompact_range hκ)).prod isCompact_univ) hcl ?_
    rintro ⟨p, k⟩ hpk
    rw [SetLike.mem_coe, MulAction.mem_stabilizer_iff, hsmul, mul_one] at hpk
    exact ⟨⟨k, (mul_inv_eq_one.mp hpk).symm⟩, Set.mem_univ _⟩
  have key : ∀ ρ : Measure G, (∀ p ∈ P, ρ.map (fun y => p * y) = ρ) →
      (∀ k, ρ.map (fun y => y * κ k) = ρ) →
      ∀ (h : P × K) (s : Set G), MeasurableSet s → ρ ((fun y => h • y) ⁻¹' s) = ρ s := by
    intro ρ hl hr h s hs
    have e : (fun y => h • y) ⁻¹' s = (fun y => y * κ h.2⁻¹) ⁻¹' ((fun y => (h.1 : G) * y) ⁻¹' s) := by
      ext y
      simp [hsmul, mul_assoc, map_inv]
    have hs1 : MeasurableSet ((fun y => (h.1 : G) * y) ⁻¹' s) := hs.preimage (measurable_const_mul _)
    rw [e, ← Measure.map_apply (measurable_mul_const _) hs1, hr, ← Measure.map_apply (measurable_const_mul _) hs,
      hl _ h.1.2]
  have hνP : ∀ p ∈ P, ν.map (fun y => p * y) = ν := by
    rintro p ⟨q, hq, t, rfl⟩
    rw [show (fun y => q * m t * y) = (fun y => q * y) ∘ (fun y => m t * y) by ext; simp [mul_assoc],
      ← Measure.map_map (measurable_const_mul _) (measurable_const_mul _), hνm t, hνQ q hq]
  by_cases hν0 : ν = 0
  · subst hν0
    exact ⟨fun g => by simp⟩
  haveI := hνc
  obtain ⟨c1, h10, h1t, e1⟩ := map_haar_eq_smul (1 : G) hcont htr hS (Measure.haar : Measure (P × K)) ν
    (key ν hνP hνK) hν0
  obtain ⟨c2, h20, h2t, e2⟩ := map_haar_eq_smul (1 : G) hcont htr hS (Measure.haar : Measure (P × K))
    (Measure.haar : Measure G)
    (key _ (fun p _ => map_mul_left_eq_self _ p) (fun k => map_mul_right_compact κ hκ _ k)) (NeZero.ne _)
  have he : ν = (c1⁻¹ * c2) • (Measure.haar : Measure G) := by
    calc ν = c1⁻¹ • (c1 • ν) := by rw [smul_smul, ENNReal.inv_mul_cancel h10 h1t, one_smul]
      _ = c1⁻¹ • (c2 • (Measure.haar : Measure G)) := by rw [← e1, e2]
      _ = _ := by rw [smul_smul]
  rw [he]
  infer_instance

end GlobalTheory.TwoSidedInv
