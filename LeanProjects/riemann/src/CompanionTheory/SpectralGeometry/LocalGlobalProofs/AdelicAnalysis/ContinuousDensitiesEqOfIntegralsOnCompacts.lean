import Formalism.UnipotentAdelicQuotients.SWXSDefs
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
open MeasureTheory Topology Matrix
open scoped ENNReal NNReal

namespace GlobalTheory.CompanionTheory.SW

theorem not_lt_of_setLIntegral_compact_eq {X : Type} [TopologicalSpace X] [LocallyCompactSpace X]
    [T2Space X] [MeasurableSpace X] [BorelSpace X] (ν : Measure X) [IsLocallyFiniteMeasure ν]
    [ν.IsOpenPosMeasure] {B : Set X} (hB : IsOpen B) {D D' : X → ℝ≥0∞}
    (hD : ContinuousOn D B) (hD' : ContinuousOn D' B)
    (h : ∀ S : Set X, IsCompact S → S ⊆ B → ∫⁻ b in S, D b ∂ν = ∫⁻ b in S, D' b ∂ν)
    {b : X} (hb : b ∈ B) : ¬ D b < D' b := by
  intro hlt
  obtain ⟨c1, h1, h12⟩ := exists_between hlt
  obtain ⟨c2, hc, h2⟩ := exists_between h12
  have hDa : ContinuousAt D b := hD.continuousAt (hB.mem_nhds hb)
  have hD'a : ContinuousAt D' b := hD'.continuousAt (hB.mem_nhds hb)

  have hN : {x | D x < c1} ∩ {x | c2 < D' x} ∩ B ∈ 𝓝 b :=
    Filter.inter_mem (Filter.inter_mem (hDa.eventually (gt_mem_nhds h1))
      (hD'a.eventually (lt_mem_nhds h2))) (hB.mem_nhds hb)
  obtain ⟨S, hSn, hSN, hS⟩ := local_compact_nhds hN
  have hSm : MeasurableSet S := hS.isClosed.measurableSet
  have hpos : ν S ≠ 0 := (Measure.measure_pos_of_mem_nhds ν hSn).ne'
  have htop : ν S ≠ ∞ := hS.measure_lt_top.ne
  have hle1 : ∫⁻ x in S, D x ∂ν ≤ c1 * ν S := by
    rw [← setLIntegral_const]
    exact lintegral_mono_ae ((ae_restrict_iff' hSm).2
      (Filter.Eventually.of_forall fun x hx => (hSN hx).1.1.le))
  have hle2 : c2 * ν S ≤ ∫⁻ x in S, D' x ∂ν := by
    rw [← setLIntegral_const]
    exact lintegral_mono_ae ((ae_restrict_iff' hSm).2
      (Filter.Eventually.of_forall fun x hx => (hSN hx).1.2.le))
  have hmid : c1 * ν S < c2 * ν S := (ENNReal.mul_lt_mul_iff_left hpos htop).2 hc
  exact (hle1.trans_lt (hmid.trans_le hle2)).ne (h S hS fun x hx => (hSN hx).2)

theorem eq_of_setLIntegral_compact_eq :
    ∀ (X : Type) [TopologicalSpace X] [LocallyCompactSpace X] [SecondCountableTopology X]
      [T2Space X] [MeasurableSpace X] [BorelSpace X] (ν : Measure X) [IsLocallyFiniteMeasure ν]
      [ν.IsOpenPosMeasure] (B : Set X), IsOpen B → ∀ D D' : X → ℝ≥0∞, ContinuousOn D B →
      ContinuousOn D' B →
      (∀ S : Set X, IsCompact S → S ⊆ B → ∫⁻ b in S, D b ∂ν = ∫⁻ b in S, D' b ∂ν) →
      ∀ b ∈ B, D b = D' b := by
  intro X _ _ _ _ _ _ ν _ _ B hB D D' hD hD' h b hb
  exact le_antisymm
    (not_lt.1 (not_lt_of_setLIntegral_compact_eq ν hB hD' hD (fun S hS hSB => (h S hS hSB).symm) hb))
    (not_lt.1 (not_lt_of_setLIntegral_compact_eq ν hB hD hD' h hb))

end GlobalTheory.CompanionTheory.SW
