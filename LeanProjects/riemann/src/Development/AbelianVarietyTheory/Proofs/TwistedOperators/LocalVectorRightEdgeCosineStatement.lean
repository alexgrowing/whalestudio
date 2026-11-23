import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LocalVectorRightEdgeCosine
import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TensorGiven
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_vector_right_edge_cosine : GlobalTheory.FunPr.Hypotheses₂ → GlobalTheory.RowClaim.Big fun {D} _ _ _ _ {T} _ _ _ _ _ {R} ch => ∀ (t : T) (e : AE D), IsIdemSum e (locPl ch.G t) → ∀ (Φ : ch.G.Datum) (i : Fin D.R.m), IsLocVec ch.W (.chi i 0) e (ch.rm.vX i 0) (GlobalTheory.FlipStart.givenFn ch.S.B t Φ e (.right i 0)) (ch.W.cosVec i (Φ i)) := by
  first | exact @GlobalTheory.CosetRow.givenFn_isLocVec | exact GlobalTheory.CosetRow.givenFn_isLocVec | (intros; apply GlobalTheory.CosetRow.givenFn_isLocVec <;> assumption)
