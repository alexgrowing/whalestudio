import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.AnnihilatorSpannedByWeightVectors
import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ActEqZeroOfMem
open GroundTheory.Automorphic.HarishChandra GlobalTheory.CompanionTheory.PresRho
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.annihilator_spanned_by_weight_vectors : ∀ {n : ℕ} {A : Type} [AddCommGroup A] [Module ℂ A] (φ : U n →ₐ[ℂ] Module.End ℂ A) (t : A), (∀ k, φ (e (k, k)) t = rhoVec n k • t) → ∀ x : U n, φ x t = 0 → x ∈ Submodule.span ℂ {y : U n | ∃ μ : Fin n → ℤ, IsAdW μ y ∧ φ y t = 0} := by
  first | exact @GlobalTheory.CompanionTheory.PresRho.mem_span_isAdW_of_kills | exact GlobalTheory.CompanionTheory.PresRho.mem_span_isAdW_of_kills | (intros; apply GlobalTheory.CompanionTheory.PresRho.mem_span_isAdW_of_kills <;> assumption)
