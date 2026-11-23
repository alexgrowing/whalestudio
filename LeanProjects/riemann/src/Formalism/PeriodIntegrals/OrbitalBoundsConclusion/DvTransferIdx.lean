import Mathlib
import Formalism.PeriodIntegrals.DivisionRowsRationalLattice
import Formalism.PeriodIntegrals.IdxCalc
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.TransferIndices.DvTransferIdxOfIdxCalc
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.DvIdxCalc

theorem division_transfer_indices : ∃ C : ℝ, PI.Dv.Conclusion4b C := PI.Dv.TIW.dvTransferIdx_of_idxCalc division_index_calc
