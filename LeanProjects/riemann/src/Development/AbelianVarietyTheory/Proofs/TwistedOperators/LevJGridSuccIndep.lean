import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsRealFam
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.GridVertexMeasureEqOfSameNormalisation
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCombAt
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CuspAlongSmoothRows
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RowVal

theorem levJ_grid_succ_indep {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc) (t t' : T) (i j : ℕ) :
    levJ G t (.grid (i + 1) (j + 1)) = levJ G t' (.grid (i + 1) (j + 1)) := rfl

theorem levJ_top_indep {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc) (t t' : T) (j : ℕ) :
    levJ G t (.top j) = levJ G t' (.top j) := by
  cases j <;> rfl

theorem vol_row_top_indep : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc) (t t' : T) (M M' : Vol G), M.Is t → M'.Is t' → (∀ j, 1 ≤ j → j ≤ D.R.m → M.ν (.grid D.R.m j) = M'.ν (.grid D.R.m j)) ∧ ∀ j, j ≤ D.R.m → M.ν (.top j) = M'.ν (.top j) := by
  intro D T L sc G t t' M M' hM hM'
  refine ⟨fun j hj1 hjm => ?_, fun j hj => ?_⟩
  · obtain ⟨i, hi⟩ : ∃ i, D.R.m = i + 1 := ⟨D.R.m - 1, by omega⟩
    obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
    have hX : levJ G t (.grid D.R.m (j' + 1)) = levJ G t' (.grid D.R.m (j' + 1)) := by
      rw [hi]; exact levJ_grid_succ_indep G t t' i j'
    have h1 := hM.vtx (.grid D.R.m (j' + 1)) ⟨le_rfl, hjm⟩
    have h2 := hM'.vtx (.grid D.R.m (j' + 1)) ⟨le_rfl, hjm⟩
    rw [← hX] at h2
    exact GlobalTheory.HaarNorm.vol_nu_eq_of_isAt M M' _ _ h1 h2
  · have h1 := hM.vtx (.top j) hj
    have h2 := hM'.vtx (.top j) hj
    rw [← levJ_top_indep G t t' j] at h2
    exact GlobalTheory.HaarNorm.vol_nu_eq_of_isAt M M' _ _ h1 h2

end GlobalTheory.RowVal
