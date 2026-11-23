import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CartanOffBlockSubmatrix
import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.SingularValueFrame
import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.CartanCoshPower
import Formalism.LocalRingCardinality.SpanPowerMembership.SignSplitEquivInl
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cartan_off_block_submatrix : ∀ (n : ℕ) (ε : Fin n → Bool) (u : Formalism.BasicNotions.UpqT (Formalism.BasicNotions.Examples₂.CD.nT ε) (Formalism.BasicNotions.Examples₂.CD.nF ε)), ∃ X : Matrix (Fin n) (Fin n) ℂ, GlobalTheory.IndefiniteRowSideFullHecke.RealRankSubgroupMembership.IsCartan ε (Matrix.reindex (Formalism.BasicNotions.Examples₂.CD.e0 ε) (Formalism.BasicNotions.Examples₂.CD.e0 ε) (Formalism.BasicNotions.UpqT.mat u)) X ∧ GlobalTheory.IndefiniteRowSideFullHecke.RealRankSubgroupMembership.offBlock ε X = (GlobalTheory.IndefiniteRowSideFullHecke.CartanCoshPower.cartanB u).submatrix (Fintype.equivFin {i // ε i = true}) ((Equiv.subtypeEquivRight (fun i => by simp)).trans (Fintype.equivFin {i // ¬ ε i = true})) := by
  first | exact @GlobalTheory.CartanDiagSigns.cartan_reindex_diag | exact GlobalTheory.CartanDiagSigns.cartan_reindex_diag | (intros; apply GlobalTheory.CartanDiagSigns.cartan_reindex_diag <;> assumption)
