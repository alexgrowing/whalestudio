import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankMirabolicWhittakerEigenspace
import Development.AbelianVarietyTheory.Definitions.Divisors.SplitDoublingNBlock
open GlobalTheory.FinGL Formalism.L2.DIV Module
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finrank_mirabolic_whittaker_eigenspace : ∀ (F : Type) [Field F] [Fintype F] (ψ : AddChar F ℂ), ψ ≠ 1 → ∀ (k : ℕ) (P : Subgroup (GL (Fin (k + 1)) F)), (∀ g, g ∈ P ↔ ∀ j, (g : Matrix (Fin (k + 1)) (Fin (k + 1)) F) (Fin.last k) j = (1 : Matrix (Fin (k + 1)) (Fin (k + 1)) F) (Fin.last k) j) → ∀ (V : Type) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] (π : Representation ℂ P V), finrank ℂ (eig π {p | (p : GL (Fin (k + 1)) F) ∈ unipSym F (k + 1) 0 k} fun p => ψ (edgeSum (symEdge 0 k) (p : GL (Fin (k + 1)) F))) = ∑ j ∈ Finset.range (k + 1), gam (Fintype.card F) (k - j) * finrank ℂ (eig π {p | (p : GL (Fin (k + 1)) F) ∈ unip F (k + 1)} fun p => ψ (edgeSum (cutEdge (j)) (p : GL (Fin (k + 1)) F))) := by
  first | exact @GlobalTheory.FinGL.Mir.mirabolic_whittaker | exact GlobalTheory.FinGL.Mir.mirabolic_whittaker | (intros; apply GlobalTheory.FinGL.Mir.mirabolic_whittaker <;> assumption)
