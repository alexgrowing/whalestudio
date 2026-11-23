import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedConjTupleAt
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAlgebraicOfRoot
open GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.BigOn.Exp
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twisted_conj_tuple_at : GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.GlobalArtinReciprocity → GlobalTheory.Published.RayClassFieldSt → GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.CasselmanWallach → TwAdm → TwChr → GlobalTheory.BigOn.Exp.TwConj.TupAt := by
  first | exact @GlobalTheory.BigOn.Exp.TwConj.tupAt | exact GlobalTheory.BigOn.Exp.TwConj.tupAt | (intros; apply GlobalTheory.BigOn.Exp.TwConj.tupAt <;> assumption)
