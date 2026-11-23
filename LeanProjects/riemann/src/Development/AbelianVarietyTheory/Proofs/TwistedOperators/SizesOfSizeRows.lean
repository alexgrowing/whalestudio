import Mathlib
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.FormulaAt
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CuspAlongSmoothRows
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsAllTiedPerTied
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsAutFunOfMemCusp

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim MeasureTheory
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RowSizes

theorem sizes_of_sizeRows : ∀ {D : D7} (large₂ : SizeData₂ D), GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup.SizeRows large₂ → GlobalTheory.IndefiniteRowSideFullHecke.CuspAlongSmoothLifts.Sizes D := by
  intro D large₂ h
  obtain ⟨⟨Pm, _, _⟩, _, hmf, hm44, _⟩ := h
  refine ⟨?_, ?_⟩
  · have h1 := D.R.f_le_k
    have h2 : D.R.f = 2 * D.R.ord := rfl
    have h3 : D.R.r = D.R.k + D.R.m - 1 := rfl
    have h4 : 44 ^ 4 ≤ D.R.m ^ 4 := Nat.pow_le_pow_left hm44 4
    omega
  · intro τ j hj
    have hg := (Pm.nodes_gap τ j hj).1
    have hf := Pm.heightBound_ge_rank_cubic
    have hN : ((GlobalTheory.Grid.bigN D : ℕ) : ℝ) = (D.R.k : ℝ) + D.R.m * (D.R.t + (D.R.r + 6) + 1) := by
      unfold GlobalTheory.Grid.bigN GlobalTheory.Grid.sLen; push_cast; ring
    have ht : (0 : ℝ) ≤ D.R.t := Nat.cast_nonneg _
    have key : ((2 * (GlobalTheory.Grid.bigN D : ℚ) ^ 3 : ℚ) : ℝ) <
        (((D.hc τ).b ⟨j + 1, hj⟩ - (D.hc τ).b ⟨j, by omega⟩ : ℚ) : ℝ) := by
      push_cast at hg ⊢
      rw [hN]
      linarith
    exact_mod_cast key

end GlobalTheory.RowSizes
