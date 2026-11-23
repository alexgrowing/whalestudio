import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.HermitianFormUnitaryOneOne
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.DiscreteSpectrumKFiniteDecomposition
import Formalism.HarderNarasimhan.ShiftInvariance

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec
open scoped InnerProductSpace ComplexOrder ContDiff

namespace GlobalTheory.Dec

theorem exists_measurable_cutoff_fibre_integral_one (G : Type) [Group G] [TopologicalSpace G]
    [IsTopologicalGroup G] [LocallyCompactSpace G] [SecondCountableTopology G] [T2Space G]
    [MeasurableSpace G] [BorelSpace G] (N : Subgroup G) (ν : Measure G)
    (_hN : IsClosed (N : Set G)) (hν : IsHaarSub (N : Set G) ν) :
    ∃ β : G → ENNReal, Measurable β ∧ (∀ y, β y ≠ ⊤) ∧ ∀ y, ∫⁻ m, β (m⁻¹ * y) ∂ν = 1 := by
  classical
  obtain ⟨hne, hfin, hcompl, hinv⟩ := hν

  have hae : ∀ᵐ m ∂ν, m ∈ (N : Set G) := by
    rw [ae_iff]; exact hcompl

  have horb : ∀ (h : G → ENNReal) (a : G), a ∈ N → ∀ y,
      ∫⁻ z, h (z⁻¹ * (a⁻¹ * y)) ∂ν = ∫⁻ z, h (z⁻¹ * y) ∂ν := by
    intro h a ha y
    have hmap : ν.map (MeasurableEquiv.mulLeft a) = ν := hinv a ha
    calc ∫⁻ z, h (z⁻¹ * (a⁻¹ * y)) ∂ν
        = ∫⁻ z, h ((MeasurableEquiv.mulLeft a z)⁻¹ * y) ∂ν := by
          congr 1; ext z; simp [_root_.mul_inv_rev, mul_assoc]
      _ = ∫⁻ z, h (z⁻¹ * y) ∂(ν.map (MeasurableEquiv.mulLeft a)) :=
          (lintegral_map_equiv (fun z => h (z⁻¹ * y)) _).symm
      _ = ∫⁻ z, h (z⁻¹ * y) ∂ν := by rw [hmap]

  have hpos : ∀ O : Set G, IsOpen O → ∀ x ∈ O, x ∈ N → 0 < ν O := by
    intro O hO x hxO hxN
    rw [pos_iff_ne_zero]
    intro h0
    apply hne
    set U : G → Set G := fun n => (fun z => (x * n⁻¹) * z) ⁻¹' O with hU
    have hUo : ∀ n ∈ (N : Set G), IsOpen (U n) := fun n _ =>
      hO.preimage (continuous_const.mul continuous_id)
    have hU0 : ∀ n ∈ (N : Set G), ν (U n) = 0 := by
      intro n hn
      have hxn : x * n⁻¹ ∈ N := N.mul_mem hxN (N.inv_mem hn)
      have := hinv _ hxn
      rw [← this] at h0
      rwa [Measure.map_apply (measurable_const_mul _) hO.measurableSet] at h0
    obtain ⟨T, hTN, hTc, hTU⟩ := TopologicalSpace.isOpen_biUnion_countable (N : Set G) U hUo
    have hNsub : (N : Set G) ⊆ ⋃ n ∈ T, U n := by
      rw [hTU]
      intro n hn
      exact Set.mem_biUnion hn (by simpa [hU, mul_assoc] using hxO)
    have hN0 : ν (N : Set G) = 0 :=
      measure_mono_null hNsub ((measure_biUnion_null_iff hTc).2 fun n hn => hU0 n (hTN hn))
    rw [← Measure.measure_univ_eq_zero, ← Set.union_compl_self (N : Set G)]
    exact measure_union_null hN0 hcompl

  let E := CompactExhaustion.choice G
  let F : ℕ → G → ENNReal := fun k y => ∫⁻ m, (E k).indicator 1 (m⁻¹ * y) ∂ν
  have hFm : ∀ k, Measurable (F k) := by
    intro k
    refine Measurable.lintegral_prod_right' (f := fun p : G × G => (E k).indicator 1 (p.2⁻¹ * p.1)) ?_
    exact (measurable_one.indicator (E.isCompact k).isClosed.measurableSet).comp
      (measurable_snd.inv.mul measurable_fst)
  have hFeq : ∀ k y, F k y = ν ((fun m => m⁻¹ * y) ⁻¹' E k) := by
    intro k y
    rw [← lintegral_indicator_one
      ((E.isCompact k).isClosed.measurableSet.preimage (measurable_inv.mul_const y))]
    rfl
  have hFtop : ∀ k y, F k y ≠ ⊤ := by
    intro k y
    rw [hFeq]
    refine ne_of_lt (lt_of_le_of_lt (measure_mono ?_)
      (((E.isCompact k).image (f := fun u : G => y * u⁻¹)
        (continuous_const.mul continuous_inv)).measure_lt_top (μ := ν)))
    intro m hm
    exact ⟨m⁻¹ * y, hm, by simp⟩
  have hFpos : ∀ y, ∃ k, 0 < F k y := by
    intro y
    obtain ⟨k, hk⟩ := E.exists_mem_nhds y
    refine ⟨k, ?_⟩
    rw [hFeq]
    refine lt_of_lt_of_le (hpos ((fun m => m⁻¹ * y) ⁻¹' interior (E k))
      (isOpen_interior.preimage (continuous_inv.mul continuous_const)) 1 ?_ N.one_mem)
      (measure_mono (Set.preimage_mono interior_subset))
    simpa [mem_interior_iff_mem_nhds] using hk
  have hFinv : ∀ k y, ∀ᵐ m ∂ν, F k (m⁻¹ * y) = F k y := by
    intro k y
    filter_upwards [hae] with m hm
    exact horb ((E k).indicator 1) m hm y

  let w : ℕ → G → ENNReal := fun k y => (2⁻¹ : ENNReal) ^ k * (E k).indicator 1 y * (1 + F k y)⁻¹
  have hwm : ∀ k, Measurable (w k) := fun k =>
    (measurable_const.mul (measurable_one.indicator (E.isCompact k).isClosed.measurableSet)).mul
      (measurable_const.add (hFm k)).inv
  let f : G → ENNReal := fun y => ∑' k, w k y
  have hfm : Measurable f := Measurable.ennreal_tsum hwm
  let T : G → ENNReal := fun y => ∫⁻ m, f (m⁻¹ * y) ∂ν
  have hTm : Measurable T :=
    Measurable.lintegral_prod_right' (f := fun p : G × G => f (p.2⁻¹ * p.1))
      (hfm.comp (measurable_snd.inv.mul measurable_fst))
  have hTinv : ∀ y, ∀ᵐ m ∂ν, T (m⁻¹ * y) = T y := by
    intro y
    filter_upwards [hae] with m hm
    exact horb f m hm y
  have hTsum : ∀ y, T y = ∑' k, (2⁻¹ : ENNReal) ^ k * (1 + F k y)⁻¹ * F k y := by
    intro y
    show ∫⁻ m, ∑' k, w k (m⁻¹ * y) ∂ν = _
    rw [lintegral_tsum (f := fun k m => w k (m⁻¹ * y)) fun k => ((hwm k).comp (measurable_inv.mul_const y)).aemeasurable]
    congr 1; ext k
    calc ∫⁻ m, w k (m⁻¹ * y) ∂ν
        = ∫⁻ m, (2⁻¹ : ENNReal) ^ k * (1 + F k y)⁻¹ * (E k).indicator 1 (m⁻¹ * y) ∂ν := by
          apply lintegral_congr_ae
          filter_upwards [hFinv k y] with m hm
          simp only [w, hm]
          ring
      _ = (2⁻¹ : ENNReal) ^ k * (1 + F k y)⁻¹ * F k y := by
          rw [lintegral_const_mul]
          exact (measurable_one.indicator (E.isCompact k).isClosed.measurableSet).comp
            (measurable_inv.mul_const y)
  have hgeom : ∑' k : ℕ, (2⁻¹ : ENNReal) ^ k ≠ ⊤ := by
    rw [ENNReal.tsum_geometric]
    rw [ENNReal.one_sub_inv_two, inv_inv]
    exact ENNReal.ofNat_ne_top
  have hTtop : ∀ y, T y ≠ ⊤ := by
    intro y
    rw [hTsum]
    refine ne_top_of_le_ne_top hgeom (ENNReal.tsum_le_tsum fun k => ?_)
    rw [mul_assoc]
    refine mul_le_of_le_one_right' ?_
    rw [mul_comm, ← div_eq_mul_inv]
    exact ENNReal.div_le_of_le_mul (by rw [one_mul]; exact le_add_self)
  have hT0 : ∀ y, T y ≠ 0 := by
    intro y
    obtain ⟨k, hk⟩ := hFpos y
    rw [hTsum]
    refine (lt_of_lt_of_le ?_ (ENNReal.le_tsum k)).ne'
    rw [mul_assoc, mul_comm ((1 + F k y)⁻¹), ← div_eq_mul_inv]
    refine ENNReal.mul_pos (pow_ne_zero _ (ENNReal.inv_ne_zero.2 ENNReal.ofNat_ne_top)) ?_
    exact (ENNReal.div_pos_iff.2 ⟨hk.ne', ENNReal.add_ne_top.2 ⟨ENNReal.one_ne_top, hFtop k y⟩⟩).ne'
  have hfle : ∀ y, f y ≠ ⊤ := by
    intro y
    refine ne_top_of_le_ne_top hgeom (ENNReal.tsum_le_tsum fun k => ?_)
    show (2⁻¹ : ENNReal) ^ k * (E k).indicator 1 y * (1 + F k y)⁻¹ ≤ _
    rw [mul_assoc]
    refine mul_le_of_le_one_right' ?_
    refine mul_le_one' ?_ (ENNReal.inv_le_one.2 le_self_add)
    by_cases hy : y ∈ E k <;> simp [hy]
  refine ⟨fun y => f y * (T y)⁻¹, hfm.mul hTm.inv, fun y => ?_, fun y => ?_⟩
  · exact ENNReal.mul_ne_top (hfle y) (ENNReal.inv_ne_top.2 (hT0 y))
  · calc ∫⁻ m, f (m⁻¹ * y) * (T (m⁻¹ * y))⁻¹ ∂ν
        = ∫⁻ m, f (m⁻¹ * y) * (T y)⁻¹ ∂ν := by
          apply lintegral_congr_ae
          filter_upwards [hTinv y] with m hm
          rw [hm]
      _ = T y * (T y)⁻¹ := lintegral_mul_const _ (hfm.comp (measurable_inv.mul_const y))
      _ = 1 := ENNReal.mul_inv_cancel (hT0 y) (hTtop y)

end GlobalTheory.Dec
