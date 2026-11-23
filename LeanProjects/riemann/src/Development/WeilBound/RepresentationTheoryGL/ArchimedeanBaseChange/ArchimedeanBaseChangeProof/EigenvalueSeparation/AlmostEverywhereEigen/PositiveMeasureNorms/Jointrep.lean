import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.EigenvalueSeparation.AlmostEverywhereEigen.OneStepOf

open MeasureTheory Filter Topology
open scoped ENNReal

open PositivityTheory.Rg.BcB.E1 PositivityTheory.Rg.BcB.E2

namespace PositivityTheory.Rg.BcB.E2.P

namespace Jointrep

theorem geom : (∑' j : ℕ, ((2 : ℝ≥0∞)⁻¹ ^ j) ^ 2) ≠ ⊤ := by
  have h2 : (∑' j : ℕ, (2 : ℝ≥0∞)⁻¹ ^ j) ≠ ⊤ := by
    rw [ENNReal.tsum_geometric, ENNReal.one_sub_inv_two, inv_inv]
    exact ENNReal.ofNat_ne_top
  refine ne_top_of_le_ne_top h2 (ENNReal.tsum_le_tsum fun j => ?_)
  exact pow_le_of_le_one (by simp) (pow_le_one₀ (by simp) (ENNReal.inv_le_one.2 one_le_two)) two_ne_zero

theorem ae_tendsto {S : Type} [MeasurableSpace S] {ν : Measure S} (h : Lp ℂ 2 ν) (v : ℕ → Lp ℂ 2 ν)
    (hv : ∀ j, edist h (v j) < (2⁻¹ : ℝ≥0∞) ^ j) :
    ∀ᵐ s ∂ν, Tendsto (fun j => (v j : S → ℂ) s) atTop (𝓝 (h s)) := by
  let g : ℕ → S → ℝ≥0∞ := fun j s => ‖(v j : S → ℂ) s - h s‖ₑ ^ (2:ℝ)
  have gm : ∀ j, Measurable (g j) := fun j =>
    (((Lp.stronglyMeasurable (v j)).measurable.sub (Lp.stronglyMeasurable h).measurable).enorm).pow_const _
  have hint : ∀ j, ∫⁻ s, g j s ∂ν ≤ ((2⁻¹ : ℝ≥0∞) ^ j) ^ 2 := by
    intro j
    have e1 : ∫⁻ s, g j s ∂ν = eLpNorm' (fun s => (v j : S → ℂ) s - h s) 2 ν ^ (2:ℝ) :=
      lintegral_rpow_enorm_eq_rpow_eLpNorm' two_pos
    have e2 : eLpNorm' (fun s => (v j : S → ℂ) s - h s) 2 ν = edist (v j) h := by
      rw [Lp.edist_def, eLpNorm_eq_eLpNorm' two_ne_zero ENNReal.ofNat_ne_top]
      simp only [ENNReal.toReal_ofNat]
      rfl
    rw [e1, e2, ENNReal.rpow_two]
    gcongr
    rw [edist_comm]; exact (hv j).le
  have hsum : ∫⁻ s, ∑' j, g j s ∂ν ≠ ⊤ := by
    rw [lintegral_tsum fun j => (gm j).aemeasurable]
    exact ne_top_of_le_ne_top geom (ENNReal.tsum_le_tsum hint)
  filter_upwards [ae_lt_top (Measurable.ennreal_tsum gm) hsum] with s hs
  have h0 : Tendsto (fun j => g j s) atTop (𝓝 0) := ENNReal.tendsto_atTop_zero_of_tsum_ne_top hs.ne
  have h1 : Tendsto (fun j => (g j s) ^ (2⁻¹ : ℝ)) atTop (𝓝 0) := by
    have := ((ENNReal.continuous_rpow_const (y := (2⁻¹:ℝ))).tendsto 0).comp h0
    simpa [Function.comp_def] using this
  rw [tendsto_iff_edist_tendsto_0]
  refine h1.congr fun j => ?_
  simp only [g, edist_eq_enorm_sub]
  rw [← ENNReal.rpow_mul]
  norm_num

end Jointrep

open Jointrep in
theorem jointrep : JointRep := by
  classical
  intro S _ ν _ _ _
  set u := TopologicalSpace.denseSeq (Lp ℂ 2 ν) with hu
  have hex : ∀ (j : ℕ) (h : Lp ℂ 2 ν), ∃ n, edist h (u n) < (2⁻¹ : ℝ≥0∞) ^ j := by
    intro j h
    obtain ⟨y, ⟨n, rfl⟩, hy⟩ := EMetric.mem_closure_iff.1
      (TopologicalSpace.denseRange_denseSeq (Lp ℂ 2 ν) h) _
      (ENNReal.pow_pos (ENNReal.inv_pos.2 (by simp : (2 : ℝ≥0∞) ≠ ⊤)) j)
    exact ⟨n, hy⟩
  let N : ℕ → Lp ℂ 2 ν → ℕ := fun j h => Nat.find (hex j h)
  have hN : ∀ j, Measurable (N j) := fun j =>
    measurable_find (hex j) fun n => Metric.isOpen_eball.measurableSet
  refine ⟨fun h s => limUnder atTop (fun j => (u (N j h) : S → ℂ) s), ?_, fun h => ?_⟩
  · have hf : ∀ j, StronglyMeasurable (fun p : Lp ℂ 2 ν × S => (u (N j p.1) : S → ℂ) p.2) := by
      intro j
      have m : Measurable (fun q : S × ℕ => (u q.2 : S → ℂ) q.1) :=
        measurable_from_prod_countable_left fun n => (Lp.stronglyMeasurable (u n)).measurable
      exact (m.comp (measurable_snd.prodMk ((hN j).comp measurable_fst))).stronglyMeasurable
    exact (StronglyMeasurable.limUnder (l := atTop) hf).measurable
  · filter_upwards [ae_tendsto h (fun j => u (N j h)) fun j => Nat.find_spec (hex j h)] with s hs
    exact hs.limUnder_eq

end PositivityTheory.Rg.BcB.E2.P
