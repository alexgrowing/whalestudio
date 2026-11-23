import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JacquetKernelSpanTwistedCharacter
import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsCIndValue
open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.LeibPhi Topology
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.jacquet_kernel_span_twisted_character : ∀ {G G' W W' : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [Group G']
    [AddCommGroup W] [Module ℂ W] [AddCommGroup W'] [Module ℂ W']
    (H U : Subgroup G) (hUH : U ≤ H) (_ : U.Normal) (θ : U →* ℂˣ) (ι : G' →* G)
    (_ : ∀ (m : G') (n : U), ∃ h : ι m * (n : G) * (ι m)⁻¹ ∈ U, θ ⟨_, h⟩ = θ n)
    (σ : Representation ℂ H W) (q : W →ₗ[ℂ] W'), IsSmooth σ →
    (∀ w, q w = 0 ↔ w ∈ Submodule.span ℂ {y | ∃ (u : U) (v : W), y = σ ⟨u, hUH u.2⟩ v - (θ u : ℂ) • v}) →
    (∀ g : G, (∃ h ∈ H, ∃ x : G', g = h * ι x) ∨
      ∃ u : U, ∃ hx : g * (u : G) * g⁻¹ ∈ H, (∀ w, σ ⟨_, hx⟩ w = w) ∧ θ u ≠ 1) →
    (∀ O ∈ 𝓝 (1 : G), ∃ K : Subgroup G, IsOpen (K : Set G) ∧ IsCompact (K : Set G) ∧ (K : Set G) ⊆ O) →
    ∀ f : cIndSpace H σ, (∀ x, q (f.1.1.1 (ι x)) = 0) → f ∈ twKer (cInd H σ) U θ := by
  first | exact @GlobalTheory.CompanionTheory.LeibPhi.Kernel.mem_twKer_of_restrict_zero | exact GlobalTheory.CompanionTheory.LeibPhi.Kernel.mem_twKer_of_restrict_zero | (intros; apply GlobalTheory.CompanionTheory.LeibPhi.Kernel.mem_twKer_of_restrict_zero <;> assumption)
