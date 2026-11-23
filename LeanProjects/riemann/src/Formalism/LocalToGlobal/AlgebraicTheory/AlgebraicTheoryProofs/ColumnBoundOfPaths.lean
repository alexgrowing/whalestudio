import Formalism.LocalToGlobal.AlgebraicTheory.StatementStep
import Formalism.LocalToGlobal.Divisibility.JetBounds.JetBoundsProofs.ValuationOfEntryBounds
import Formalism.LocalToGlobal.Divisibility.JetBounds.JetBoundsProofs.NormEqOneOfNotMem
import Formalism.LocalToGlobal.ExponentGrids.ExponentGridsProofs.PairBoundsBalanceCondition

open Module NumberField IsDedekindDomain
open scoped BigOperators

noncomputable section

namespace Formalism.L2.AlgTh

open Formalism.DivisionValues (vw PlOver)
open Formalism.L2.Indef (DefBase DefSide DefCols)
open Formalism.L2.DIV (PathData EmbAt IsExpansion ColsInt RowsInt LastInt UnitsInt StabDvd)
open Formalism.AtG (PerBd colRhs)

theorem column_bound_of_paths : ColBoundOfPaths := by
  intro K _ _ _ Bs Df Dc u t Nu w g _ pb Dg Rg hw hpb hG
  obtain ⟨ι, X, D, j1, hι, hX, hc, hr, hl, hu, hD, hgD, he⟩ := hG
  have hpl : Formalism.EigenvalueLevelCeiling.plc w = g := Formalism.L2.DIV.embeddingForces_holds K w g ι hι
  have hram : Formalism.EigenvalueLevelCeiling.ramw w = vw w (g : K) := by
    unfold Formalism.EigenvalueLevelCeiling.ramw
    rw [hpl]
  have hr1 : (1 : ℝ) ≤ (Formalism.EigenvalueLevelCeiling.ramw w : ℝ) := by exact_mod_cast (Formalism.EigenvalueLevelCeiling.ramBasic K w).2.1
  have hr0 : (Formalism.EigenvalueLevelCeiling.ramw w : ℝ) ≠ 0 := by linarith
  have hq0 : 0 < ‖(g : ℂ_[g])‖ := Formalism.DworkPowerSeriesWeights.norm_l_pos g
  have main : PerBd Dc u Nu t w (-(∑ j, (Dg j : ℝ) * (vw w pb : ℝ)) - (∑ j, Rg j) * (vw w (g : K) : ℝ)) := by
    refine Formalism.L2.DIV.valuation_of_entry_bounds Dc u t Nu w _ g ι X D j1
      (fun j => -((Dg j : ℝ) * (vw w pb : ℝ) / (Formalism.EigenvalueLevelCeiling.ramw w : ℝ)) - Rg j) hι hX hc hr hl hu hD ?_ ?_
    · intro π j
      have h := he π j
      rw [hι pb hpb, ← Real.rpow_natCast, ← Real.rpow_mul hq0.le, mul_assoc, ← Real.rpow_add hq0] at h
      have hpos : 0 < ‖(g : ℂ_[g])‖ ^ ((vw w pb : ℝ) / (Formalism.EigenvalueLevelCeiling.ramw w : ℝ) * (Dg j : ℝ) + Rg j) :=
        Real.rpow_pos_of_pos hq0 _
      have h2 : ‖X.e π j‖ ≤ (‖(g : ℂ_[g])‖ ^ ((vw w pb : ℝ) / (Formalism.EigenvalueLevelCeiling.ramw w : ℝ) * (Dg j : ℝ) + Rg j))⁻¹ := by
        rw [← one_div, le_div_iff₀ hpos]
        exact h
      rw [← Real.rpow_neg hq0.le] at h2
      refine h2.trans (le_of_eq ?_)
      congr 1
      ring
    · rw [padicValNat.eq_zero_of_not_dvd hgD, ← hram]
      have hterm : ∀ j, (Formalism.EigenvalueLevelCeiling.ramw w : ℝ) * (-((Dg j : ℝ) * (vw w pb : ℝ) / (Formalism.EigenvalueLevelCeiling.ramw w : ℝ)) - Rg j
          - ((0 : ℕ) : ℝ)) = -((Dg j : ℝ) * (vw w pb : ℝ)) - Rg j * (Formalism.EigenvalueLevelCeiling.ramw w : ℝ) := by
        intro j
        field_simp
        push_cast
        ring
      rw [Finset.mul_sum, Finset.sum_congr rfl (fun j _ => hterm j), Finset.sum_sub_distrib,
        Finset.sum_neg_distrib, Finset.sum_mul]
  exact ⟨main, fun Jx sx nn cg E0 h => Formalism.AtG.UnitPeriodBounds.perBd_mono h main⟩

theorem column_right_side_le : ColRhsLe := by
  intro K _ _ w g hw J _ pb cg Dg Rg E0 hpb hcg hR
  unfold colRhs
  have hc : (vw w cg : ℝ) = 0 := by
    obtain ⟨k, hk, hk1⟩ := hcg
    exact_mod_cast Formalism.AtG.root_of_unity_valuation_zero K cg k hk hk1 w
  have hp : ∀ j, (vw w (pb ^ Dg j) : ℝ) = (Dg j : ℝ) * (vw w pb : ℝ) := by
    intro j
    rw [Formalism.AtG.PlacesLyingOver.vw_pow' w pb hpb]
    push_cast
    ring
  have hv : (0 : ℝ) < (vw w (g : K) : ℝ) := by exact_mod_cast hw
  simp only [hp, hc]
  have := mul_le_mul_of_nonneg_right hR hv.le
  linarith

end Formalism.L2.AlgTh
