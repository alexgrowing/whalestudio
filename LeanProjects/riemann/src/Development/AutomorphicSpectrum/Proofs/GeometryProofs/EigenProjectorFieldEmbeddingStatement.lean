import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.EigenProjectorFieldEmbedding
import Mathlib
open NumberField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eigen_projector_field_embedding : ∀ (E : Type) [Field E] [NumberField E] (K : Type) [Field K] [CharZero K] (σ : 𝓞 E →+* K), ∃ (n : ℕ) (e : Fin n → 𝓞 E) (c : Fin n → K), ∑ k, c k * σ (e k) = 1 ∧ ∀ (L W : Type) [Field L] [AddCommGroup W] [Module L W] (j : K →+* L) (ρ : 𝓞 E →+* Module.End L W) (a : 𝓞 E) (w : W), ρ a (∑ k, j (c k) • ρ (e k) w) = j (σ a) • ∑ k, j (c k) • ρ (e k) w := by
  first | exact @GlobalTheory.CompanionTheory.TraceProj.exists_eigen_projector | exact GlobalTheory.CompanionTheory.TraceProj.exists_eigen_projector | (intros; apply GlobalTheory.CompanionTheory.TraceProj.exists_eigen_projector <;> assumption)
