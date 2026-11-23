import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IsOpenAdditiveCharacterKernel
open Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isOpen_additive_character_kernel : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ψ : AddChar k Circle), Continuous ψ → IsOpen {x : k | ψ x = 1} := by
  first | exact @GlobalTheory.CompanionTheory.LocalFieldChar.isOpen_addChar_ker | exact GlobalTheory.CompanionTheory.LocalFieldChar.isOpen_addChar_ker | (intros; apply GlobalTheory.CompanionTheory.LocalFieldChar.isOpen_addChar_ker <;> assumption)
