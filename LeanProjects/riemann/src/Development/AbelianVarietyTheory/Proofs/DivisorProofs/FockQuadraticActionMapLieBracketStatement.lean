import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockQuadraticActionMapLieBracket
import Formalism.LocalRingCardinality.DataTheta
open Formalism.BasicNotions.TH
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fockQuadraticAction_map_lie_bracket : ∀ (p q r s : ℕ) (Y Z : Matrix (Ln p q r s) (Ln p q r s) ℂ), omAct p q r s (Y * Z - Z * Y) = omAct p q r s Y * omAct p q r s Z - omAct p q r s Z * omAct p q r s Y := by
  first | exact @GlobalTheory.FockLie.omAct_lie | exact GlobalTheory.FockLie.omAct_lie | (intros; apply GlobalTheory.FockLie.omAct_lie <;> assumption)
