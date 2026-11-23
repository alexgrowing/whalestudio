import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.T2SpaceNumberFieldInfiniteAdeles
open NumberField IsDedekindDomain MeasureTheory Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.GaugeEx Filter
open scoped TensorProduct NNReal ENNReal Pointwise

namespace GlobalTheory.GaugeEx

theorem continuous_distribHaarChar_units (R : Type) [CommRing R]
    [TopologicalSpace R] [IsTopologicalRing R] [T2Space R] [LocallyCompactSpace R]
    [SecondCountableTopology R] [MeasurableSpace R] [BorelSpace R] :
    Continuous (fun u : Rˣ => distribHaarChar R u) := by
  let μ : Measure R := Measure.addHaar
  obtain ⟨K, hKc, hK0⟩ := exists_compact_mem_nhds (0 : R)
  have h0 : μ K ≠ 0 := (Measure.measure_pos_of_mem_nhds μ hK0).ne'
  have ht : μ K ≠ ⊤ := hKc.measure_lt_top.ne
  have hup : ∀ c : ℝ≥0, 1 < c → ∃ V ∈ 𝓝 (1 : R), ∀ u : Rˣ, (u : R) ∈ V → distribHaarChar R u < c := by
    intro c hc
    have hlt : μ K < (c : ℝ≥0∞) * μ K := by
      calc μ K = 1 * μ K := (one_mul _).symm
        _ < _ := (ENNReal.mul_lt_mul_iff_left h0 ht).2 (by exact_mod_cast hc)
    obtain ⟨U, hKU, hUo, hU⟩ := Set.exists_isOpen_lt_of_lt K _ hlt
    obtain ⟨V, hV, hVS⟩ := compact_open_separated_mul_left hKc hUo hKU
    refine ⟨V, hV, fun u hu => ?_⟩
    have h1 : μ (u • K) ≤ μ U := by
      refine measure_mono ?_
      rintro _ ⟨x, hx, rfl⟩
      exact hVS ⟨u, hu, x, hx, rfl⟩
    rw [← distribHaarChar_mul μ u K] at h1
    have h3 := (ENNReal.mul_lt_mul_iff_left h0 ht).1 (h1.trans_lt hU)
    exact_mod_cast h3
  refine continuous_of_continuousAt_one (distribHaarChar R : Rˣ →* NNReal) ?_
  rw [ContinuousAt, map_one, tendsto_order]
  constructor
  · intro a ha
    by_cases ha0 : a = 0
    · subst ha0
      exact Eventually.of_forall fun u => distribHaarChar_pos
    have hap : 0 < a := pos_iff_ne_zero.2 ha0
    obtain ⟨V, hV, h⟩ := hup a⁻¹ ((one_lt_inv₀ hap).2 ha)
    have e2 : ∀ᶠ u : Rˣ in 𝓝 1, ((u⁻¹ : Rˣ) : R) ∈ V :=
      Units.continuous_coe_inv.continuousAt.eventually
        (show V ∈ 𝓝 (((1 : Rˣ)⁻¹ : Rˣ) : R) by simpa using hV)
    filter_upwards [e2] with u hu
    have := h _ hu
    rw [map_inv] at this
    exact (inv_lt_inv₀ distribHaarChar_pos hap).1 this
  · intro c hc
    obtain ⟨V, hV, h⟩ := hup c hc
    have e1 : ∀ᶠ u : Rˣ in 𝓝 1, (u : R) ∈ V :=
      Units.continuous_val.continuousAt.eventually (show V ∈ 𝓝 ((1 : Rˣ) : R) by simpa using hV)
    filter_upwards [e1] with u hu using h u hu

theorem modu_units (S : Type) [CommRing S] [TopologicalSpace S] [IsTopologicalRing S]
    [LocallyCompactSpace S] (u : Sˣ) : modu S (u : S) = distribHaarChar S u := by
  simp [modu]

theorem modu_basic : ∀ (S : Type) [CommRing S] [TopologicalSpace S] [IsTopologicalRing S] [T2Space S] [LocallyCompactSpace S] [SecondCountableTopology S] [MeasurableSpace S] [BorelSpace S], (∀ u : S, IsUnit u → 0 < modu S u ∧ ∀ ν : Measure S, ν.IsAddHaarMeasure → ν = modu S u • ν.map (fun z => u * z)) ∧ (∀ u w : S, IsUnit u → IsUnit w → modu S (u * w) = modu S u * modu S w) ∧ modu S 1 = 1 ∧ (IsOpenUnits S → ContinuousOn (modu S) {u | IsUnit u}) := by
  intro S _ _ _ _ _ _ _ _
  refine ⟨?_, ?_, ?_, ?_⟩
  · rintro _ ⟨u, rfl⟩
    rw [modu_units]
    refine ⟨distribHaarChar_pos, fun ν hν => ?_⟩
    ext s hs
    have e : (fun z : S => (u : S) * z) ⁻¹' s = u⁻¹ • s := by
      ext z
      rw [Set.mem_inv_smul_set_iff]; rfl
    rw [Measure.smul_apply, Measure.map_apply (measurable_const_mul _) hs, e, ENNReal.smul_def,
      smul_eq_mul, distribHaarChar_mul, smul_inv_smul]
  · rintro _ _ ⟨u, rfl⟩ ⟨w, rfl⟩
    rw [← Units.val_mul, modu_units, modu_units, modu_units, map_mul]
  · rw [← Units.val_one, modu_units, map_one]
  · intro hS
    rintro _ ⟨u, rfl⟩
    have hoe : IsOpenEmbedding (Units.val : Sˣ → S) := IsOpenUnits.isOpenEmbedding_unitsVal
    refine ContinuousAt.continuousWithinAt ?_
    rw [← hoe.continuousAt_iff]
    have : modu S ∘ Units.val = fun u : Sˣ => distribHaarChar S u := funext (modu_units S)
    rw [this]
    exact (continuous_distribHaarChar_units S).continuousAt

end GlobalTheory.GaugeEx
