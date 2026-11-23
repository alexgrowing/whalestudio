import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AmpleNsmul
import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MemSupportBDIff
open GlobalTheory GlobalTheory.ProjVar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.ample_nsmul_of_pos : ∀ (F : Type) [Field F] (Y : Var F) (Δ : Y.Dv) (n : ℕ), 0 < n → Y.ample Δ → Y.ample (n • Δ) := by
  first | exact @GlobalTheory.ProjVar.Var.ample_nsmul | exact GlobalTheory.ProjVar.Var.ample_nsmul | (intros; apply GlobalTheory.ProjVar.Var.ample_nsmul <;> assumption)
