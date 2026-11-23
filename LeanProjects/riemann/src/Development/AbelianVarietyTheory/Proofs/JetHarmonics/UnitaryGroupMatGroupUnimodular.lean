import Mathlib
import Development.AbelianVarietyTheory.Definitions.Jets.SideFam
import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
import Formalism.PeriodIntegrals.QuotSetU
import Formalism.PeriodIntegrals.QuotInv
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnitaryQuotientCompactness.MaximalCompactIsCompact
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ExistsIsFolnerUWset
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.MatGroupHaarUniqueFiniteCompactOpenPosStatement

open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory

theorem unitaryGroup_matGroup_unimodular : ∀ (k r : ℕ), PI.IsMatGroup (GG k r) ∧
    ∀ μG : Measure (Formalism.QuantumDeterminants.Mt k r), PI.BesselPeriodGGP.IsHaarOn (GG k r) μG →
      PI.IsHaarOnM (GG k r) μG ∧ PI.IsRightInvM (GG k r) μG := by
  intro k r
  have hG : PI.IsMatGroup (GG k r) := PI.QuotSetU.UnitaryGroupMassFormula.unitary_hermitian_group k r
  refine ⟨hG, fun μG hμ => ?_⟩
  have hμ' : PI.IsHaarOnM (GG k r) μG := hμ
  refine ⟨hμ', ?_⟩
  obtain ⟨μ, h1, h2, -⟩ := GlobalTheory.SgInf.exists_unimod_GG (k := k) (r := r)
  have h1' : PI.IsHaarOnM (GG k r) μ := h1
  obtain ⟨c, -, -, hc⟩ := (GlobalTheory.T.matGroupHaar_unique_finite_compact_openPos _ (GG k r) μ hG h1').1 μG hμ'
  intro s hs
  have h3 : μ.map (PI.rmulQ s) = μ := h2 s hs
  rw [hc, Measure.map_smul, h3]

end GlobalTheory
