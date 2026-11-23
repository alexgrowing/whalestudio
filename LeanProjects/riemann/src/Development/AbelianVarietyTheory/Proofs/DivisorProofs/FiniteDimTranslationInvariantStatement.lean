import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteDimTranslationInvariant
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemNilRad
open Matrix GlobalTheory.TorFin
open scoped ContDiff

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_dim_translation_invariant : ∀ (G : Type) [Group G] (W : Submodule ℂ (G → ℂ)) (γ : ℝ → G), FiniteDimensional ℂ W → γ 0 = 1 → (∀ ψ ∈ W, ∃ ψ' ∈ W, ∀ (g : G) (t : ℝ), HasDerivAt (fun τ : ℝ => ψ (γ τ * g)) (ψ' (γ t * g)) t) → ∀ ψ ∈ W, ∀ t : ℝ, (fun g => ψ (γ t * g)) ∈ W := by
  first | exact @GlobalTheory.TransODE.main | exact GlobalTheory.TransODE.main | (intros; apply GlobalTheory.TransODE.main <;> assumption)
