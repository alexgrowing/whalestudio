import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.QuantumDetAdjointForm
import Formalism.RealPlaceAnalysis.ThirdArithmeticHolds
open Formalism.REAL
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.quantum_det_adjoint_form : ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (B : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ) (n : ℕ) (X Y : Fin n → Fin n → Module.End ℂ V), Formalism.REAL.GlRel Y → (∀ (i j : Fin n) (φ ψ : V), B (X i j φ) ψ = -B φ (Y i j ψ)) → ∀ (v : ℂ) (φ ψ : V), B (Formalism.REAL.qdet X v φ) ψ = B φ ((((-1 : ℂ) ^ n) • Formalism.REAL.qdet Y ((n : ℂ) - 1 - (starRingEnd ℂ) v)) ψ) := by
  first | exact @GlobalTheory.CompanionTheory.CapelliAdj.adj_qdet | exact GlobalTheory.CompanionTheory.CapelliAdj.adj_qdet | (intros; apply GlobalTheory.CompanionTheory.CapelliAdj.adj_qdet <;> assumption)
