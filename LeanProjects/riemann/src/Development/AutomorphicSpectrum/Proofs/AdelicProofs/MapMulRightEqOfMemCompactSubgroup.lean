import Mathlib

open MeasureTheory
open scoped ENNReal Pointwise

namespace GlobalTheory.CompanionTheory.Xa1

theorem map_mul_right_eq_of_mem_compact_subgroup :
    ∀ (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G] [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G] (μ : Measure G), μ.IsMulLeftInvariant → IsFiniteMeasureOnCompacts μ → ∀ K : Subgroup G, IsCompact (K : Set G) → ∀ k ∈ K, μ.map (fun x => x * k) = μ := by
  intro G _ _ _ _ _ _ _ _ μ hinv hfin K hK k hk
  let ν : Measure G := Measure.haar
  have hmeas : Measurable (fun x : G => x * k) := measurable_mul_const k
  have key : ν.map (fun x => x * k) = ν := by
    obtain ⟨C, hC, hC1⟩ := exists_compact_mem_nhds (1 : G)
    have hS : IsCompact (C * (K : Set G)) := hC.mul hK
    have hsub : C ⊆ C * (K : Set G) := fun x hx => ⟨x, hx, 1, K.one_mem, mul_one x⟩
    have hpos : ν (C * (K : Set G)) ≠ 0 :=
      ((Measure.measure_pos_of_mem_nhds ν hC1).trans_le (measure_mono hsub)).ne'
    have htop : ν (C * (K : Set G)) ≠ ⊤ := hS.measure_lt_top.ne
    have hpre : (fun x : G => x * k) ⁻¹' (C * (K : Set G)) = C * (K : Set G) := by
      ext x
      constructor
      · rintro ⟨c, hc, l, hl, h⟩
        refine ⟨c, hc, l * k⁻¹, K.mul_mem hl (K.inv_mem hk), ?_⟩
        simp only at h ⊢
        rw [← mul_assoc, h, mul_inv_cancel_right]
      · rintro ⟨c, hc, l, hl, rfl⟩
        exact ⟨c, hc, l * k, K.mul_mem hl hk, (mul_assoc _ _ _).symm⟩
    haveI : IsFiniteMeasureOnCompacts (ν.map (fun x => x * k)) :=
      ⟨fun L hL => by
        rw [Measure.map_apply hmeas hL.measurableSet]
        exact ((Homeomorph.mulRight k).isCompact_preimage.2 hL).measure_lt_top⟩
    have h1 := Measure.isMulLeftInvariant_eq_smul (ν.map (fun x => x * k)) ν
    set c := Measure.haarScalarFactor (ν.map (fun x => x * k)) ν with hc
    have h2 : (ν.map (fun x => x * k)) (C * (K : Set G)) = ν (C * (K : Set G)) := by
      rw [Measure.map_apply hmeas hS.measurableSet, hpre]
    rw [h1, Measure.smul_apply, ENNReal.smul_def, smul_eq_mul] at h2
    have h3 : (c : ℝ≥0∞) = 1 := by
      have := (ENNReal.mul_left_inj hpos htop).1 (h2.trans (one_mul _).symm)
      exact this
    have h4 : c = 1 := by exact_mod_cast h3
    rw [h1, h4, one_smul]
  have h := Measure.isMulLeftInvariant_eq_smul μ ν
  rw [h, Measure.map_smul, key]

end GlobalTheory.CompanionTheory.Xa1
