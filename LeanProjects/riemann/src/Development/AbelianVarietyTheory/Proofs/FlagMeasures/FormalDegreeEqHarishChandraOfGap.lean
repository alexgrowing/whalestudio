import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.SzHypFD
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.FinalClosed
import Formalism.SharpRestriction.CuspSpanNormBounds.FrobeniusCoefficientMemLp.DegIUp
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HarishChandraFormalDegreeCompactDualLargeGapsStatement

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S

namespace GlobalTheory

theorem dsig_eq_fdegHC_of_gap : ∀ (D : D7), Ties D → ∀ (τ : D.what₂.Tau) (h : ℝ),
    Formalism.QuantumDeterminants.IsHCParam (lamSH D.R (D.hc τ)) → Formalism.QuantumDeterminants.GapAtLeast (epsSH D.R) (lamSH D.R (D.hc τ)) h →
    Formalism.MainNotions.GapDS.thrE (epsSH D.R) + 1 < h → D.dsig τ = Formalism.QuantumDeterminants.fdegHC (lamSH D.R (D.hc τ)) := by
  intro D hT τ h hlam hg hth
  have e : max (((2 * D.R.rS + D.R.k + 1 : ℕ) : ℝ) * (ReciprocityTheory.ChartRestriction.DS.pOf (epsSH D.R) : ℝ) *
        (ReciprocityTheory.ChartRestriction.DS.qOf (epsSH D.R) : ℝ) + 1)
      (16 * ((2 * D.R.rS + D.R.k + 1 : ℕ) : ℝ) * (ReciprocityTheory.ChartRestriction.DS.S7.q0 (epsSH D.R) : ℝ) +
        8 * Real.sqrt (2 * (ReciprocityTheory.ChartRestriction.DS.S7.q0 (epsSH D.R) : ℝ))) = Formalism.MainNotions.GapDS.thrE (epsSH D.R) := by
    unfold Formalism.MainNotions.GapDS.thrE Formalism.MainNotions.GapDS.thrDS ReciprocityTheory.ChartRestriction.DS.S7.q0
    rfl
  have hth' := e ▸ (by linarith : Formalism.MainNotions.GapDS.thrE (epsSH D.R) < h)
  obtain ⟨H, i1, i2, σ, hσ, -⟩ := ReciprocityTheory.ChartRestriction.DS.dsExistsG_closed _ (epsSH D.R) _ hlam h hg hth'
  have hpq := Formalism.MainNotions.S.Pv.DegI.minpq_pos D
  have hp : 1 ≤ ReciprocityTheory.ChartRestriction.DS.pOf (epsSH D.R) := le_trans hpq (min_le_left _ _)
  have hq : 1 ≤ ReciprocityTheory.ChartRestriction.DS.qOf (epsSH D.R) := le_trans hpq (min_le_right _ _)
  have htrue : ∃ a, epsSH D.R a = true := by
    unfold ReciprocityTheory.ChartRestriction.DS.pOf at hp
    obtain ⟨a, ha⟩ := Finset.card_pos.mp (Nat.lt_of_lt_of_le Nat.zero_lt_one hp)
    exact ⟨a, (Finset.mem_filter.mp ha).2⟩
  have hfalse : ∃ a, epsSH D.R a = false := by
    unfold ReciprocityTheory.ChartRestriction.DS.qOf at hq
    obtain ⟨a, ha⟩ := Finset.card_pos.mp (Nat.lt_of_lt_of_le Nat.zero_lt_one hq)
    exact ⟨a, (Finset.mem_filter.mp ha).2⟩
  have hd := GlobalTheory.T.harishChandra_formalDegree_compactDual_large_gaps D.cd D.s.cdScale hT.cdScale_tie _ (epsSH D.R) _ h hlam htrue hfalse hg hth H σ hσ
  exact (hT.dsig_tie τ H σ _ hσ hd).symm

end GlobalTheory
