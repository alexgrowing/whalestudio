import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemisimpleEquivariantProjectionUnique
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToEndDApply
open GlobalTheory.LocFinIso
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.semisimple_equivariant_projection_unique : ∀ (G : Type) [Group G] (K : Set G) (V : Type) [AddCommGroup V] [Module ℂ V] (ρ : G →* Module.End ℂ V) (D : Submodule ℂ V) (h1 : (1 : G) ∈ K) (hmul : ∀ k ∈ K, ∀ k' ∈ K, k * k' ∈ K) (hst : ∀ k ∈ K, ∀ x ∈ D, ρ k x ∈ D), IsSemisimpleModule (MonoidAlgebra ℂ (subK K h1 hmul)) (repD ρ D K h1 hmul hst).asModule → ∀ (P : (repD ρ D K h1 hmul hst).asModule →ₗ[MonoidAlgebra ℂ (subK K h1 hmul)] (repD ρ D K h1 hmul hst).asModule), (∀ v, P (P v) = P v) → (∀ g : (repD ρ D K h1 hmul hst).asModule →ₗ[MonoidAlgebra ℂ (subK K h1 hmul)] (repD ρ D K h1 hmul hst).asModule, ∀ v, P (g v) = g (P v)) → ∀ (m : ℕ) (b : Fin m → V) (A : G → Matrix (Fin m) (Fin m) ℂ) (hbD : ∀ i, b i ∈ D), LinearIndependent ℂ b → (∀ k ∈ K, ∀ j, ρ k (b j) = ∑ i, A k i j • b i) → (∀ k ∈ K, A k ∈ Matrix.unitaryGroup (Fin m) ℂ) → ∃ Pm : Matrix (Fin m) (Fin m) ℂ, (∀ j, ((toEndD ρ D K h1 hmul hst P ⟨b j, hbD j⟩ : D) : V) = ∑ i, Pm i j • b i) ∧ star Pm = Pm := by
  first | exact @GlobalTheory.LocFinIso.hermitian_matrix_of_commuting_idempotent | exact GlobalTheory.LocFinIso.hermitian_matrix_of_commuting_idempotent | (intros; apply GlobalTheory.LocFinIso.hermitian_matrix_of_commuting_idempotent <;> assumption)
