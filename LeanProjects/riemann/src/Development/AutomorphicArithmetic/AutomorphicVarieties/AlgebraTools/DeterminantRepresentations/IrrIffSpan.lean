import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.IrreducibleSpans.Burnside
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.IrrIffSpan

open Polynomial Matrix

theorem UpperTheory.V.AlgebraTools.Det.irrIffSpan :
    ∀ {K G ι : Type} [Field K] [IsAlgClosed K] [Group G] [Fintype ι] [DecidableEq ι] (ρ : G →* Matrix ι ι K),
    (∀ N : Submodule K (ι → K), (∀ g, ∀ v ∈ N, ρ g *ᵥ v ∈ N) → N = ⊥ ∨ N = ⊤) ↔ Submodule.span K (Set.range ρ) = ⊤ :=
  _root_.UpperTheory.Reformulated.B.Qe4.irrIffSpan
