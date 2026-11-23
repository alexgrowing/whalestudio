import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LatticeSpanProjectionBound
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GlueApplyOfNotInFibre
open GlobalTheory.CompanionTheory.Ar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lattice_span_projection_bound : ∀ (Ω Ω₀ : Type) [Field Ω] [Field Ω₀] (i : Ω₀ →+* Ω) (Li Li₀ : Type) [AddCommGroup Li] [Module Ω Li] [AddCommGroup Li₀] [Module Ω₀ Li₀] (ι : Li₀ →+ Li), IsExtOver i ι → Submodule.span Ω (Set.range ι) = ⊤ → ∀ (W : Subring Ω) (L₀ : Set Li₀) (L : Set Li) (r : ℕ) (b : Fin r → Li) (b₀ : Fin r → Li₀) (π₀ : Fin r → Module.Dual Ω₀ Li₀) (T : Module.End Ω Li) (Dn κ : Ω) (m : Ω₀), Submodule.span W L = Submodule.span W (ι '' L₀) → (∀ e ∈ L, T e ∈ Submodule.span W (Set.range b)) → (∀ j, T (ι (b₀ j)) = Dn • ι (b₀ j)) → (∀ j, m • b₀ j ∈ L₀) → (∀ a j, π₀ a (b₀ j) = if a = j then 1 else 0) → (∀ a, ∀ e ∈ L₀, i (m * π₀ a e) ∈ W) → (∀ j, κ • b j ∈ L) → (∀ j, b j ∈ Submodule.span Ω (Set.range fun a => ι (b₀ a))) → (∀ j, (Dn * i m) • ι (b₀ j) ∈ Submodule.span W (Set.range b)) ∧ ∀ j, (i m * κ) • b j ∈ Submodule.span W (Set.range fun a => ι (b₀ a)) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Frames.two_frames | exact GlobalTheory.CompanionTheory.Ar.Frames.two_frames | (intros; apply GlobalTheory.CompanionTheory.Ar.Frames.two_frames <;> assumption)
