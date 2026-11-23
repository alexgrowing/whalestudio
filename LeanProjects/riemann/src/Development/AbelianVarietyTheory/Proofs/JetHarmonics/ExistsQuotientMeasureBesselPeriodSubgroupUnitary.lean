import Mathlib
import Development.AbelianVarietyTheory.Definitions.Jets.SideFam
import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
import Formalism.PeriodIntegrals.QuotSetU
import Formalism.PeriodIntegrals.QuotInv
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsQuotientMeasureWeilStatement
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.UnitaryGroupMatGroupUnimodularStatement
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.BesselSubgroupProductMeasureIsHaarStatement

open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory

theorem exists_isQuotMeas_bessel_subgroup : ∀ (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ)
    (μW μN μG : Measure (Formalism.QuantumDeterminants.Mt k r)), Formalism.QuantumDeterminants.inWb k r z → 0 < Formalism.QuantumDeterminants.Tz k r z →
    PI.BesselPeriodGGP.IsHaarOn (Formalism.QuantumDeterminants.UWset k r z) μW →
    PI.BesselPeriodGGP.IsHaarOn (Formalism.QuantumDeterminants.Nset k r) μN →
    PI.BesselPeriodGGP.IsHaarOn (GG k r) μG →
    ∃ νq, PI.BesselPeriodGGP.IsQuotMeas μG (muSof μW μN) νq := by
  intro k r z μW μN μG hz hT hW hN hG
  obtain ⟨hGgrp, hGinv⟩ := GlobalTheory.T.isMatGroup_GG_and_haar_right_invariant k r
  obtain ⟨hGhaar, _⟩ := hGinv μG hG
  obtain ⟨hSgrp, hSsub, hShaar, hSright⟩ := GlobalTheory.T.besselSubgroup_product_measure_isHaar k r z μW μN hz hT hW hN
  exact GlobalTheory.T.exists_quotientMeasure_weil (2 * r + k + 1) (GG k r) (Formalism.QuantumDeterminants.Sset k r z) μG (muSof μW μN)
    hGgrp hSgrp hSsub hGhaar hShaar hSright

end GlobalTheory
