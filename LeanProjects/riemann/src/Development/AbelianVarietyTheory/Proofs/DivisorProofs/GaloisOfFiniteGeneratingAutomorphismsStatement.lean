import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GaloisOfFiniteGeneratingAutomorphisms
import Mathlib
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isGalois_of_finite_fixed_automorphisms : ∀ (K K' : Type) [Field K] [Field K'] (i : K →+* K'), i.Finite → ∀ (Γ : Type) [Finite Γ] (s : Γ → (K' ≃+* K')), (∀ g x, s g (i x) = i x) → (∀ y : K', (∀ g, s g y = y) → y ∈ i.range) → (letI := i.toAlgebra; IsGalois K K') ∧ ∀ σ : K' ≃+* K', (∀ x, σ (i x) = i x) → σ ∈ Submonoid.closure (Set.range s) := by
  first | exact @GlobalTheory.galois_of_finite_generating_automorphisms | exact GlobalTheory.galois_of_finite_generating_automorphisms | (intros; apply GlobalTheory.galois_of_finite_generating_automorphisms <;> assumption)
