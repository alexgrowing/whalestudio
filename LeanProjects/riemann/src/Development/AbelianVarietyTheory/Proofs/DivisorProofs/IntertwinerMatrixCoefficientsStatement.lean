import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntertwinerMatrixCoefficients
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToEndDApply
open GlobalTheory.LocFinIso
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.intertwiner_matrix_coefficients : ∀ (G : Type) [Group G] (K : Set G) (V : Type) [AddCommGroup V] [Module ℂ V] (ρ : G →* Module.End ℂ V) (D : Submodule ℂ V) (m : ℕ) (b : Fin m → V) (A : G → Matrix (Fin m) (Fin m) ℂ) (hbD : ∀ i, b i ∈ D) (f : Fin m → (D →ₗ[ℂ] D)), (∀ k ∈ K, ∀ j, ρ k (b j) = ∑ i, A k i j • b i) → (∀ j, ∀ k ∈ K, ∀ u v : D, (v : V) = ρ k u → (f j v : V) = ρ k (f j u)) → ∃ T : EuclideanSpace ℂ (Fin (m * m)) →ₗ[ℂ] V, (∀ k ∈ K, ∀ v, T (leftMul A k v) = ρ k (T v)) ∧ ∑ j, ((f j ⟨b j, hbD j⟩ : D) : V) ∈ LinearMap.range T := by
  first | exact @GlobalTheory.IntwLeftMul.exists_intertwiner | exact GlobalTheory.IntwLeftMul.exists_intertwiner | (intros; apply GlobalTheory.IntwLeftMul.exists_intertwiner <;> assumption)
