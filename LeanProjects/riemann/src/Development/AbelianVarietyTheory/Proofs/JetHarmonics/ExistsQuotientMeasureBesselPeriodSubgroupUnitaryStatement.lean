import Mathlib
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsQuotientMeasureBesselPeriodSubgroupUnitary
import Development.AbelianVarietyTheory.Definitions.Jets.SideFam
import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
import Formalism.PeriodIntegrals.QuotSetU
import Formalism.PeriodIntegrals.QuotInv
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_quotientMeasure_besselPeriodSubgroup_unitary : ∀ (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (μW μN μG : Measure (Formalism.QuantumDeterminants.Mt k r)), Formalism.QuantumDeterminants.inWb k r z → 0 < Formalism.QuantumDeterminants.Tz k r z → PI.BesselPeriodGGP.IsHaarOn (Formalism.QuantumDeterminants.UWset k r z) μW → PI.BesselPeriodGGP.IsHaarOn (Formalism.QuantumDeterminants.Nset k r) μN → PI.BesselPeriodGGP.IsHaarOn (GG k r) μG → ∃ νq, PI.BesselPeriodGGP.IsQuotMeas μG (muSof μW μN) νq := by
  first | exact @GlobalTheory.exists_isQuotMeas_bessel_subgroup | exact GlobalTheory.exists_isQuotMeas_bessel_subgroup | (intros; apply GlobalTheory.exists_isQuotMeas_bessel_subgroup <;> assumption)
