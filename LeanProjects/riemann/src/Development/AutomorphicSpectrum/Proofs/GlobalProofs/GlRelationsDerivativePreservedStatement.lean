import Mathlib
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.GlRelationsDerivativePreserved
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DiscreteSpectrumOfResidual
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.gl_relations_triangular_annihilation : ∀ (W Q : Type) [AddCommGroup W] [Module ℂ W] [AddCommGroup Q] [Module ℂ Q] (c N : ℕ) (n : Fin c → ℕ) (h : ∑ i, n i = N)
    (Xf : Fin N → Fin N → Module.End ℂ W), Formalism.REAL.GlRel Xf → ∀ Wn : Submodule ℂ W, (∀ p q, ∀ F ∈ Wn, Xf p q F ∈ Wn) →
    ∀ L : W →ₗ[ℂ] Q, (∀ p q, GlobalTheory.SmGL.blk (GlobalTheory.SmGL.stdBlocks n h) p < GlobalTheory.SmGL.blk (GlobalTheory.SmGL.stdBlocks n h) q → ∀ F ∈ Wn, L (Xf p q F) = 0) →
    ∀ W₀ : Set W, W₀ ⊆ Wn → (∀ v : ℂ, ∃ s : ℂ, ∀ F ∈ W₀, Formalism.REAL.qdet Xf v F = s • F) →
    ∀ (i : Fin c) (w : ℂ), ∃ q : Polynomial ℂ, q.Monic ∧ ∀ F ∈ W₀,
      L (Polynomial.aeval (Formalism.REAL.qdet (fun p q : Fin (n i) => Xf (GlobalTheory.SmGL.stdBlocks n h ⟨i, p⟩) (GlobalTheory.SmGL.stdBlocks n h ⟨i, q⟩)) w) q F) = 0 := by
  first | exact @GlobalTheory.CompanionTheory.Dblock.CentreManyBlocks.monic_relations_along_block | exact GlobalTheory.CompanionTheory.Dblock.CentreManyBlocks.monic_relations_along_block | (intros; apply GlobalTheory.CompanionTheory.Dblock.CentreManyBlocks.monic_relations_along_block <;> assumption)
