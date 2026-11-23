import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PhiPullBaseComm
import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TranslationInv
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullFullL
open Matrix MeasureTheory Set Filter Topology
open GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe GlobalTheory.TorsionForm GlobalTheory.TorsionForm.OneVec
open scoped Real ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.phi_pull_base_comm : ∀ {n : ℕ} (a : Fin n → ℂ) (y : Ext (n + n)), phi (pullBaseL a y) = pullBaseL a (phi y) := by
  first | exact @GlobalTheory.TorsionForm.OneVec.phi_pullBaseL | exact GlobalTheory.TorsionForm.OneVec.phi_pullBaseL | (intros; apply GlobalTheory.TorsionForm.OneVec.phi_pullBaseL <;> assumption)
