import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemGLintIffMatrixImageStandardLatticeEq
import Mathlib
import Formalism.SatakeDualWeyl.Statement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemMatLat
open Polynomial Matrix GlobalTheory.LatOrb
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_GLint_iff_matrixImage_standardLattice_eq : ∀ {K : Type} [Field K] (V : ValuationSubring K) (n : ℕ) (k : GL (Fin n) K),
    k ∈ Formalism.UG.GLint (Fin n) V.toSubring ↔ matLat V k.val (stdLat V n) = stdLat V n := by
  first | exact @GlobalTheory.LatOrb.mem_GLint_iff_matLat_std | exact GlobalTheory.LatOrb.mem_GLint_iff_matLat_std | (intros; apply GlobalTheory.LatOrb.mem_GLint_iff_matLat_std <;> assumption)
