import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PositiveFormOrthonormalBasisUnitary
import Mathlib
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.positive_form_orthonormal_basis_unitary : ∀ (Wt : Type) [AddCommGroup Wt] [Module ℂ Wt] (S : Submodule ℂ Wt) [FiniteDimensional ℂ S] (Bf : S →ₗ⋆[ℂ] S →ₗ[ℂ] ℂ), (∀ x y, Bf y x = starRingEnd ℂ (Bf x y)) → (∀ x, x ≠ 0 → 0 < (Bf x x).re) → ∃ (m : ℕ) (b : Fin m → S), (∀ i j, Bf (b i) (b j) = if i = j then 1 else 0) ∧ Submodule.span ℂ (Set.range b) = ⊤ ∧ ∀ T : S →ₗ[ℂ] S, (∀ x y, Bf (T x) (T y) = Bf x y) → (∀ j, T (b j) = ∑ i, Bf (b i) (T (b j)) • b i) ∧ Matrix.of (fun i j => Bf (b i) (T (b j))) ∈ Matrix.unitaryGroup (Fin m) ℂ := by
  first | exact @GlobalTheory.hermitian_onb_unitary | exact GlobalTheory.hermitian_onb_unitary | (intros; apply GlobalTheory.hermitian_onb_unitary <;> assumption)
