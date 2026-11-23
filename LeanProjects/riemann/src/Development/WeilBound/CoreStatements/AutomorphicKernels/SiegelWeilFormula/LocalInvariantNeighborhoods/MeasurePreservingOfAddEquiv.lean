import Mathlib

namespace PositivityTheory.SiegelWeilFormula.OswLocFin

open MeasureTheory

theorem measurePreserving_of_addEquiv {G : Type*} [AddCommGroup G] [TopologicalSpace G]
    [IsTopologicalAddGroup G] [LocallyCompactSpace G] [T2Space G] [SecondCountableTopology G]
    [MeasurableSpace G] [BorelSpace G] (μ : MeasureTheory.Measure G) [μ.IsAddHaarMeasure]
    (e : G ≃+ G) (he : Continuous e) (he' : Continuous e.symm) (B : Set G) (hB : IsCompact B)
    (hB' : (interior B).Nonempty) (heB : e ⁻¹' B = B) :
    MeasureTheory.MeasurePreserving e μ μ := by
  have hm : Measurable e := he.measurable
  have : (μ.map e).IsAddHaarMeasure := e.isAddHaarMeasure_map μ he he'
  obtain ⟨c, hcμ⟩ : ∃ c : NNReal, μ.map e = c • μ := ⟨_, Measure.isAddLeftInvariant_eq_smul (μ.map e) μ⟩
  have hBm : MeasurableSet B := hB.isClosed.measurableSet
  have hval : μ.map e B = μ B := by rw [Measure.map_apply hm hBm, heB]
  have hpos : μ B ≠ 0 := (Measure.measure_pos_of_nonempty_interior μ hB').ne'
  have hfin : μ B ≠ ⊤ := hB.measure_lt_top.ne
  have hc : c = 1 := by
    have h1 := congrArg (fun ν : Measure G => ν B) hcμ
    simp only [Measure.smul_apply, hval, ENNReal.smul_def, smul_eq_mul] at h1
    have h2 : (c : ENNReal) * μ B = 1 * μ B := by rw [one_mul]; exact h1.symm
    have h3 : (c : ENNReal) = 1 := (ENNReal.mul_left_inj hpos hfin).1 h2
    exact_mod_cast h3
  refine ⟨hm, ?_⟩
  rw [hcμ, hc, one_smul]

end PositivityTheory.SiegelWeilFormula.OswLocFin
