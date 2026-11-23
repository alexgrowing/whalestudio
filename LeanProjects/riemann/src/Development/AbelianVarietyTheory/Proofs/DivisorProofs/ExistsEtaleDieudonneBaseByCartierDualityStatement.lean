import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEtaleDieudonneBaseByCartierDuality
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.RedSurjective
open CategoryTheory GlobalTheory.PDiv GlobalTheory.PDivGroup
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_etaleDieudonneBase_by_cartierDuality : ∀ (p : ℕ) [Fact p.Prime] (Bc : GlobalTheory.Dieu.Base p (fun _ _ G => G.IsConn)), ∃ Be : GlobalTheory.Dieu.Base p (fun _ _ G => G.IsEt), Be.EtDual Bc := by
  first | exact @GlobalTheory.dieuBase_isEt_of_isConn | exact GlobalTheory.dieuBase_isEt_of_isConn | (intros; apply GlobalTheory.dieuBase_isEt_of_isConn <;> assumption)
