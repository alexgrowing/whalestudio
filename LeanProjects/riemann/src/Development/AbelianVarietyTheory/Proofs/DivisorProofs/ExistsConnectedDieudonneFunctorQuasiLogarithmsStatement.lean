import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsConnectedDieudonneFunctorQuasiLogarithms
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.RedSurjective
open CategoryTheory GlobalTheory.PDiv GlobalTheory.PDivGroup
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_connected_dieudonne_functor_quasiLogarithms : ∀ (p : ℕ) [Fact p.Prime], ∃ B : GlobalTheory.Dieu.Base p (fun _ _ G => G.IsConn), B.Katz := by
  first | (exact @GlobalTheory.exists_base_isConn_katz) | (exact GlobalTheory.exists_base_isConn_katz) | (intros; apply GlobalTheory.exists_base_isConn_katz  <;> assumption)
