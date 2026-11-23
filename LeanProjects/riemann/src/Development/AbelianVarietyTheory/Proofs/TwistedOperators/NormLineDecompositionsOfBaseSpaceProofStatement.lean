import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NormLineDecompositionsOfBaseSpaceProof
import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.FlatSpaceComponents
open Formalism.BasicNotions Formalism.BasicNotions.TH NumberField IsDedekindDomain
open scoped nonZeroDivisors
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.normLineDecompositionsOfBaseSpace_proof : ∀ D : D7, GlobalTheory.IndefiniteRowSideFullHecke.FlatSpaceComponents.RecordDecSt D := by
  first | exact @GlobalTheory.Proof.normLineDecompositionsOfBaseSpace_proof.recordDec | exact GlobalTheory.Proof.normLineDecompositionsOfBaseSpace_proof.recordDec | (intros; apply GlobalTheory.Proof.normLineDecompositionsOfBaseSpace_proof.recordDec <;> assumption)
