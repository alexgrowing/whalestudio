import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AdelicLatticeSelfDualHermitian
import Formalism.SharpRestriction.CuspSpanNormBounds.GlobAut
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ExistsReduction
open MeasureTheory Formalism.MainNotions.S GlobalTheory.RowLev NumberField IsDedekindDomain Matrix
open scoped InnerProductSpace ComplexOrder TensorProduct Pointwise Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.adelicLattice_selfDual_hermitian : ∀ (I : AutInst) (y : Fin I.n → (I.E ⊗[I.F] Af I.F)), y ∈ I.Lf ↔ ∀ y' ∈ I.Lf, hAf I y' y ∈ IntAf I.F I.E := by
  first | exact @GlobalTheory.AdelicLattice.adelicLattice_selfDual | exact GlobalTheory.AdelicLattice.adelicLattice_selfDual | (intros; apply GlobalTheory.AdelicLattice.adelicLattice_selfDual <;> assumption)
