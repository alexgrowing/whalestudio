import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NilradicalAdjointExpStable
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemNilRad
open Matrix GlobalTheory.TorFin
open scoped ContDiff

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.nilradical_adjoint_exp_stable : ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) ℂ), Jᴴ = J → IsUnit J.det → ∀ (x : Fin n → ℂ) (Y : Matrix (Fin n) (Fin n) ℂ), Y ∈ nilRad J x → J⁻¹ * Yᴴ * J ∈ nilRad J x ∧ NormedSpace.exp Y - 1 ∈ nilRad J x := by
  first | exact @GlobalTheory.TorFin.NilAdj.nilRad_adj_exp | exact GlobalTheory.TorFin.NilAdj.nilRad_adj_exp | (intros; apply GlobalTheory.TorFin.NilAdj.nilRad_adj_exp <;> assumption)
