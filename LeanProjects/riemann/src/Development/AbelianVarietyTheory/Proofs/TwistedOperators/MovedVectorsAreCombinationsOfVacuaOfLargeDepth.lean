import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsRealFam
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCombAt
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CuspAlongSmoothRows
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MovedFiniteDatumEqHeisenbergCombinationVacuumStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LastRowMovedVacuumEqUnitMulChosenStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsColumnUnitVacuaFamilyMovedStatement

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.RowUnf GlobalTheory.RowChain GlobalTheory.SeeSaw GlobalTheory.RowVal GlobalTheory.RowReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.RowVal

theorem comb_smul_heis {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (c : WO S T →₀ ℂ) (a : ℂ) (f : WO S T → ℂ) :
    comb ψ S T c (a • f) = a • comb ψ S T c f := by
  have h : ∀ u, heisO ψ S T u (a • f) = a • heisO ψ S T u f := fun u => by
    funext w; simp only [heisO, Pi.smul_apply, smul_eq_mul]; ring
  unfold comb
  rw [Finset.smul_sum]
  exact Finset.sum_congr rfl fun u _ => by rw [h, smul_comm]

theorem movedAt_big : Big fun ch => MovedAt ch := by
  refine ⟨0, fun ε CF _ => ⟨0, fun D large₂ _ _ Γ _ _ Pl0 T A Ks _ _ _ R F hS ch hIs _ => ?_⟩⟩
  obtain ⟨v, hv, κ, z, hz, hcol⟩ := GlobalTheory.T.exists_columnUnitVacuaFamily_moved large₂ F hS ch hIs
  choose κ' hκ' using fun i : Fin D.R.m => GlobalTheory.T.lastRow_moved_vacuum_eq_unit_mul_chosen large₂ F hS ch hIs i i.2
  refine ⟨v, hv, κ, fun i => if h : i < D.R.m then κ' ⟨i, h⟩ else 1, z, hz,
    fun t a β τ c hSum hExp hC d hd => ⟨fun j => ?_, fun i => ?_⟩⟩
  · have hvec := ((hSum.vec β τ hExp d hd).1 j)
    obtain ⟨e, -, hd1, -⟩ := hExp
    have hz1 := ((hd1 d hd).1 j).2.2
    rw [GlobalTheory.T.movedFiniteDatum_eq_heisenbergCombination_vacuum large₂ F hS ch hIs t (.top t j) (show DefPair D.R.m (Pair.top t (j : ℕ) : Pair T) from j.2) (d.1 j) ((c d).1 j) hz1 hvec ((hC d hd).1 j),
      hcol t j j.2, comb_smul_heis]
  · have hvec := ((hSum.vec β τ hExp d hd).2 i)
    obtain ⟨e, -, hd1, -⟩ := hExp
    have hz1 := ((hd1 d hd).2 i).2.2
    rw [GlobalTheory.T.movedFiniteDatum_eq_heisenbergCombination_vacuum large₂ F hS ch hIs t (.chi i D.R.m) (show DefPair D.R.m (Pair.chi (i : ℕ) D.R.m : Pair T) from ⟨i.2, rfl⟩) (d.2 i) ((c d).2 i) hz1 hvec ((hC d hd).2 i),
      hκ' i, comb_smul_heis]
    simp only [dif_pos i.2, combR]

end GlobalTheory.RowVal

end
