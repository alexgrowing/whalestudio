import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsUnitVectorOrthogonalInstanceRankThree
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.GaugeUnfold
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.GaussMean
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_unit_vector_orthogonal_instance_rank_three : ∀ (I : AutInst) (P Q : ℕ), HasSig I P Q → 3 ≤ I.n → ∀ s : Bool, (if s then 1 ≤ P else 1 ≤ Q) → ∃ (I' : AutInst) (e : I'.E ≃+* I.E) (x : Fin I.n → I.E) (A : Matrix (Fin I.n) (Fin I'.n) I.E) (xf : I.Gf), IsPerpInst I I' e s x A xf ∧ HasSig I' (if s then P - 1 else P) (if s then Q else Q - 1) := by
  first | exact @GlobalTheory.PerpInst.exists_isPerpInst | exact GlobalTheory.PerpInst.exists_isPerpInst | (intros; apply GlobalTheory.PerpInst.exists_isPerpInst <;> assumption)
