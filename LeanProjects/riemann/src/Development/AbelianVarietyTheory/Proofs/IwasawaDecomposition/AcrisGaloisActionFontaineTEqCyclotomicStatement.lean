import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AcrisGaloisActionFontaineTEqCyclotomic
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsCrisP
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.acrisGaloisAction_fontaine_t_eq_cyclotomic : ∀ (l : ℕ) [Fact l.Prime], ∀ (C : Core l) (g : GQ l), sigA g C.t = algebraMap (Per.Ainf l) (Per.Acris l) (Per.zA l (C.χ g : ℤ_[l])) * C.t := by
  first | exact @GlobalTheory.MemLoc.TAct.t_act | exact GlobalTheory.MemLoc.TAct.t_act | (intros; apply GlobalTheory.MemLoc.TAct.t_act <;> assumption)
