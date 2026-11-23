import Mathlib
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.CartanDecompositionGlNonarchimedean
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.EntryMulSubOne
open Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cartan_decomposition_gl_nonarchimedean : ∀ (L : Type) [NontriviallyNormedField L] [IsUltrametricDist L] [ProperSpace L] (n : ℕ) (p : Lˣ), GlobalTheory.CompanionTheory.CartGL.IsUnif p → ∀ g : GL (Fin n) L, ∃ a : Fin n → ℤ, Antitone a ∧ ∃ k₁ ∈ GlobalTheory.CompanionTheory.CartGL.congK L n 1 zero_le_one le_rfl, ∃ k₂ ∈ GlobalTheory.CompanionTheory.CartGL.congK L n 1 zero_le_one le_rfl, g = k₁ * GlobalTheory.CompanionTheory.CartGL.dPow p a * k₂ := by
  first | exact @GlobalTheory.CompanionTheory.CartGL.cartan_unitBall | exact GlobalTheory.CompanionTheory.CartGL.cartan_unitBall | (intros; apply GlobalTheory.CompanionTheory.CartGL.cartan_unitBall <;> assumption)
