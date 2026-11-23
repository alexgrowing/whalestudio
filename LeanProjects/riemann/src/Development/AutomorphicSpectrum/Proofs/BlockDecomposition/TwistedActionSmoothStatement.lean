import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TwistedActionSmooth
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.UnipotentDerivatives.DerUnipLeUnipB
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.BZMir
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twisted_action_smooth : ∀ {G M V : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [Group M] [TopologicalSpace M] [IsTopologicalGroup M] [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V), IsSmooth ρ → ∀ (N : Subgroup G) (θ : N →* ℂˣ) (s : M →* G), Continuous s → ∀ (hs : ∀ (m : M) (n : N), ∃ h : s m * (n : G) * (s m)⁻¹ ∈ N, θ ⟨_, h⟩ = θ n), IsSmooth (twAct ρ N θ s hs) := by
  first | exact @GlobalTheory.CompanionTheory.BZMir.twAct_isSmooth | exact GlobalTheory.CompanionTheory.BZMir.twAct_isSmooth | (intros; apply GlobalTheory.CompanionTheory.BZMir.twAct_isSmooth <;> assumption)
