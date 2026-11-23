import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjAlgApply
open Matrix Polynomial

namespace GlobalTheory

theorem unitary_conj_ker_basis_gram {K : Type} [Field K] (σ : K →+* K) {n : ℕ} (γ g : GL (Fin n) K)
    (hg : ((g : Matrix (Fin n) (Fin n) K).map σ)ᵀ * (g : Matrix (Fin n) (Fin n) K) = 1)
    (Q : K[X]) {ι : Type} (u : ι → Fin n → K) (hu : LinearIndependent K u)
    (hspan : Submodule.span K (Set.range u) =
      LinearMap.ker (Matrix.toLin' (aeval ((g⁻¹ * γ * g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) Q))) :
    LinearIndependent K (fun i => (g : Matrix (Fin n) (Fin n) K) *ᵥ u i) ∧
    Submodule.span K (Set.range fun i => (g : Matrix (Fin n) (Fin n) K) *ᵥ u i) =
      LinearMap.ker (Matrix.toLin' (aeval (γ : Matrix (Fin n) (Fin n) K) Q)) ∧
    (Matrix.of fun i j => ∑ k, σ (((g : Matrix (Fin n) (Fin n) K) *ᵥ u i) k) *
        ((g : Matrix (Fin n) (Fin n) K) *ᵥ u j) k) = Matrix.of fun i j => ∑ k, σ (u i k) * u j k := by
  first
  | exact @_root_.GlobalTheory.ConjugateAlgebraLemmas.main
  | exact _root_.GlobalTheory.ConjugateAlgebraLemmas.main
  | (apply _root_.GlobalTheory.ConjugateAlgebraLemmas.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.ConjugateAlgebraLemmas.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.ConjugateAlgebraLemmas.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.ConjugateAlgebraLemmas.main ..)

end GlobalTheory
