import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HomogeneousClassSubstitution
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasTotalBiChains
open CategoryTheory Limits Opposite AlgebraicTopology GlobalTheory.EZ
universe u v
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.diagonal_differential_eval : ∀ {C : Type u} [Category.{v} C] [Preadditive C] (Y : SimplicialObject (SimplicialObject C)) (n : ℕ), (ev Y).map (dD (n + 1) n) = (diagCx Y).d (n + 1) n := by
  first | (exact @GlobalTheory.EZ.ev_map_dD_eq_diagCx_d) | (exact GlobalTheory.EZ.ev_map_dD_eq_diagCx_d) | (intros; apply GlobalTheory.EZ.ev_map_dD_eq_diagCx_d <;> assumption)
