import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RankInsertLeAddTwo
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConeIntZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HaarOIsAddHaar
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GoodModelEigenContinuous
open MeasureTheory Filter NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ConeSoB GlobalTheory.StdPairLoc
open scoped Matrix GlobalTheory.VacAny
attribute [local instance] GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.measFv GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.borelFv
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rank_insert_le_add_two : ∀ {R : Type} [Field R] {a b : ℕ} (Y : Matrix (Fin b) (Fin (a + b)) R) (r : Fin (a + (b + 2)) → R) (c : Fin b → R) (x : R),
    (insS Y r c x).rank ≤ Y.rank + 2 := by
  first | exact @GlobalTheory.StdPairLoc.insS_rank_le | exact GlobalTheory.StdPairLoc.insS_rank_le | (intros; apply GlobalTheory.StdPairLoc.insS_rank_le <;> assumption)
