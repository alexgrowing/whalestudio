import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteImageCompactRightInvariant
import Mathlib
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_image_compact_right_invariant : ∀ {Γ X : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] (K : Set Γ), IsCompact K → ∀ Gf : Γ → X, {s : Γ | ∀ x, Gf (x * s) = Gf x} ∈ nhds (1 : Γ) → (Gf '' K).Finite := by
  first | exact @GlobalTheory.CompanionTheory.TopGroup.finite_image_of_right_invariant_near_one | exact GlobalTheory.CompanionTheory.TopGroup.finite_image_of_right_invariant_near_one | (intros; apply GlobalTheory.CompanionTheory.TopGroup.finite_image_of_right_invariant_near_one <;> assumption)
