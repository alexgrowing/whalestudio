import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.LocalWeightCharts.NotMidCases
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.LocalWeightCharts.WavePacketL1L2

noncomputable section

open MeasureTheory

namespace WlocSk

open HM

theorem uw_finite {k r : ℕ} (z : Fin (2 * r + k + 1) → ℂ) (hz : Formalism.QuantumDeterminants.inWb k r z)
    (hT : 0 < Formalism.QuantumDeterminants.Tz k r z) : IsFiniteMeasure (hmeas (Formalism.QuantumDeterminants.UWset k r z) (uw_clsub z)) := by
  have : CompactSpace (Grp (Formalism.QuantumDeterminants.UWset k r z : Set (Mx k r)) (uw_clsub z)) :=
    isCompact_iff_compactSpace.mp (compactW z hz hT)
  refine ⟨?_⟩
  unfold hmeas
  rw [Measure.map_apply (val_cemb _ _).continuous.measurable MeasurableSet.univ, Set.preimage_univ]
  exact isCompact_univ.measure_lt_top

theorem haar_measure_unipotent_nilradical : HaarWN := by
  intro k r z hz hT
  exact ⟨hmeas (Formalism.QuantumDeterminants.UWset k r z) (uw_clsub z), haarNm k r, hmeas_haar _ _, haarNm_haar,
    uw_finite z hz hT, haarNm_compact⟩

end WlocSk
