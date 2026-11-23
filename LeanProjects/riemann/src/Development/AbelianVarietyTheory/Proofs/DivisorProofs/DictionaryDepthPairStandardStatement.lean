import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DictionaryDepthPairStandard
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjPlInvolutive
open GlobalTheory.SumSize GlobalTheory.RowClaim GlobalTheory.SumSize.OppConj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.dictionary_depth_pair_standard : GlobalTheory.FunPr.Hypotheses₂ → (∀ D, GlobalTheory.NormSum.Inp D) → DictK → DepthK → PairStdK := by
  first | exact @GlobalTheory.KerConjMean.pairStdK | exact GlobalTheory.KerConjMean.pairStdK | (intros; apply GlobalTheory.KerConjMean.pairStdK <;> assumption)
