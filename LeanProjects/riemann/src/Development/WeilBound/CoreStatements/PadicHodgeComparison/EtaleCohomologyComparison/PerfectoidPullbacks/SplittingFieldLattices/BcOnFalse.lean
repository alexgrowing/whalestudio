import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.SplittingFieldLattices.Kh3
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.SplittingFieldLattices.SplitField
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.GrCechFin
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.GlobalSerreRelations.Transport

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open CategoryTheory AlgebraicGeometry TensorProduct GlobalTheory.LogCris DividedPowers

namespace CrystallineSemistableComparison.Pb

theorem bcOn_true : BcOn True := bc_loc @loc_bc @poly_tf

theorem bcOn_false : BcOn False := bc_glob @glob_bc_st bcOn_true

theorem kh1 : KH.LocGr := @loc_gr

theorem kh2 : KH.GlobSerreSt := @glob_serre_st

set_option maxHeartbeats 4000000 in
theorem finO' : True ∧ FinO := ⟨trivial, fin_o kh1 @poly_tf kh2 kh3.2⟩

theorem afgA : AfgA := afg_a bcOn_false finO'.2

theorem liftA : LiftA := lift_a afgA

theorem basisB : BasisB := basis_b bcOn_false @k_iso

end CrystallineSemistableComparison.Pb
