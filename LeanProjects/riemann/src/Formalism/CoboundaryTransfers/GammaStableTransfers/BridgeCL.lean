import Formalism.CoboundaryTransfers.StatementBridge
import Formalism.WachModuleLifts.WachModuleProofs.WachModuleStatementHolds

noncomputable section

namespace Formalism.CoboundaryTransfers

open Formalism

theorem baseOfCL_qLin {p : ℕ} [Fact p.Prime] {A : Type} [CommRing A] [Algebra ℤ_[p] A]
    (B : CL.W.Base p A) : (baseOfCL B).QLin := by
  show B.q = B.π₀ + ((p : ℕ) : A)
  rw [B.hq, map_natCast]

theorem wach_lattice_nonempty_Q : NonemptyQ := by
  intro p _
  obtain ⟨W, hN, hX⟩ := CL.W.wach_module_nonempty p
  refine ⟨baseOfCL (CL.W.polyBase p), ofCL W, rfl, hN, hX, ?_, baseOfCL_qLin _,
    (CL.W.polyBase p).hφ⟩
  show ¬ IsUnit (Polynomial.X + Polynomial.C (p : ℤ_[p]))
  exact Polynomial.not_isUnit_X_add_C _

end Formalism.CoboundaryTransfers
