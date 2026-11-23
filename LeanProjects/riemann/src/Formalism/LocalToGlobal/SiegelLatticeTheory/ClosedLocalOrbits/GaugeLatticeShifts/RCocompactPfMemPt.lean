import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.RCocompactPfMemSteps
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.NilradicalLatticeZMemSpan

noncomputable section

open scoped Classical
open Matrix NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp
open Formalism.L2.SG.Pf.UnipB Formalism.L2.SG.Pf.Unip

namespace Formalism.L2.SG.TermOp.Vanish

theorem memPtOf_holds : MemPtOf := by
  intro D X Z n hni hn
  obtain ⟨x, hx⟩ := Formalism.L2.SG.Pf.ratPt_holds D X n hni
  refine ⟨x, hx, fun v => ?_⟩
  obtain ⟨M', -, h1, -, h3⟩ := hx
  have hM : (M' : Matrix (Fin X.B.I.n) (Fin X.B.I.n) X.B.I.E) = gE X Z := by
    apply Matrix.ext_of_mulVec_single
    intro i
    obtain ⟨y, hy⟩ := Formalism.L2.SG.Pf.crd_surj X (Pi.single i 1)
    rw [← hy, ← h3, hn]
  unfold Mv
  rw [h1 v, hM, gE_real]
  simp only [← Matrix.mul_assoc, Bv'_mul_Bv, Matrix.one_mul]
  rw [Matrix.mul_assoc, Bv'_mul_Bv, Matrix.mul_one, cay_map]

end Formalism.L2.SG.TermOp.Vanish
