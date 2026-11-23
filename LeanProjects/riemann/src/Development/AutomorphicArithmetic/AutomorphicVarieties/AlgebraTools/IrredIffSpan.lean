import Mathlib
import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.IrreducibleSpans.Burnside
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.SpanMapRingHomEqTop
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.IrreducibleOfSpanningMatrices

open Polynomial Matrix IsLocalRing TensorProduct

private theorem irreducible_of_span_eq_top {K G ι : Type} [Field K] [Fintype ι] [DecidableEq ι]
    (f : G → Matrix ι ι K) (h : Submodule.span K (Set.range f) = ⊤) (N : Submodule K (ι → K))
    (hN : ∀ g, ∀ v ∈ N, (f g).mulVec v ∈ N) : N = ⊥ ∨ N = ⊤ :=
  _root_.UpperTheory.Reformulated.B.IrreducibleOfSpanningMatrices.irreducible_of_span_eq_top f h N hN

private theorem span_map_ringHom_eq_top {k K G ι : Type} [Field k] [Field K] [Fintype ι] [DecidableEq ι]
    (φ : k →+* K) (f : G → Matrix ι ι k) (h : Submodule.span k (Set.range f) = ⊤) :
    Submodule.span K (Set.range fun g => (f g).map φ) = ⊤ :=
  _root_.UpperTheory.Reformulated.B.Qe1.span_map_ringHom_eq_top φ f h

theorem UpperTheory.V.AlgebraTools.irred_iff_span :
    ∀ {k K G : Type} [Field k] [IsAlgClosed k] [Field K] [Group G] {ι : Type} [Fintype ι] [DecidableEq ι] (φ : k →+* K) (ρ : G →* Matrix ι ι k), ((∀ N : Submodule k (ι → k), (∀ g, ∀ v ∈ N, (ρ g).mulVec v ∈ N) → N = ⊥ ∨ N = ⊤) ↔ Submodule.span k (Set.range ρ) = ⊤) ∧ (Submodule.span k (Set.range ρ) = ⊤ ↔ Submodule.span K (Set.range fun g => (ρ g).map φ) = ⊤) ∧ (Submodule.span K (Set.range fun g => (ρ g).map φ) = ⊤ → ∀ N : Submodule K (ι → K), (∀ g, ∀ v ∈ N, ((ρ g).map φ).mulVec v ∈ N) → N = ⊥ ∨ N = ⊤) := by
  intro k K G _ _ _ _ ι _ _ φ ρ
  refine ⟨⟨KStar.Schema.span_eq_top_of_irreducible ρ, fun h N hN => irreducible_of_span_eq_top ρ h N hN⟩,
    ⟨span_map_ringHom_eq_top φ ρ, fun h => ?_⟩, fun h N hN => irreducible_of_span_eq_top _ h N hN⟩
  refine KStar.Schema.span_eq_top_of_residue φ ?_ _ ?_
  · rw [IsLocalRing.maximalIdeal_eq_bot]
    exact (RingHom.injective_iff_ker_eq_bot φ).mp φ.injective
  · rw [← Set.range_comp]
    exact h
