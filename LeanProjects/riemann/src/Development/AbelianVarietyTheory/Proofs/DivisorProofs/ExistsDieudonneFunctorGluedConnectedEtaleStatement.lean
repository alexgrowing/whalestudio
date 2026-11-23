import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDieudonneFunctorGluedConnectedEtale
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.RedSurjective
open CategoryTheory GlobalTheory.PDiv GlobalTheory.PDivGroup
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_dieudonneFunctor_glued_connected_etale : ∀ (p : ℕ) [Fact p.Prime] (Bc : GlobalTheory.Dieu.Base p (fun _ _ G => G.IsConn)) (Be : GlobalTheory.Dieu.Base p (fun _ _ G => G.IsEt)), Bc.Katz → Be.EtDual Bc → ∃ B : GlobalTheory.Dieu.Base p (fun _ _ _ => True), B.Katz ∧ B.EtDual B := by
  first | exact @GlobalTheory.Dieu.Glue.exists_katz_etDual | exact GlobalTheory.Dieu.Glue.exists_katz_etDual | (intros; apply GlobalTheory.Dieu.Glue.exists_katz_etDual <;> assumption)
