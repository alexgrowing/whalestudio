import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntertwinerFixesOfLocalVacuum
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsHeisTrivial
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SumOpTransversal
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HeisenbergIntertwiningSumsCompEqIndex
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.NormalizedHeisenbergIntertwinerComp
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIntertwinerHeisenbergCocycleOfFixedVector
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsWeilRepresentationHeisenberg
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SpanHeisenbergTranslatesVacuumEqTop
open Classical GlobalTheory.FinWeil
open scoped BigOperators
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.intertwiner_fixes_of_local_vacuum' : ∀ {R X M : Type} [CommRing R] [AddCommGroup X] [Module R X] [AddCommGroup M] [Module ℂ M] {σ : R →+* R} {w : R} {γ : X → X → ℂ} {W : X → M →ₗ[ℂ] M}, IsHeis σ w γ W → ∀ A : Submodule R X, SelfDual γ A → Submodule.span ℂ {m : M | ∃ x e, Fixes W A e ∧ m = W x e} = ⊤ → ∀ (φ : X →ₗ[R] X) (T : M →ₗ[ℂ] M), (∀ x v, T (W x v) = W (φ x) (T v)) → (∀ e, Fixes W A e → T e = e) → ∀ P : X →ₗ[R] X, (∀ x y, γ (P x) y = γ x (P y)) → (∀ a ∈ A, P a ∈ A) → (∀ x, φ (x - P x) = x - P x) → ∀ m : M, (∀ a ∈ A, W (P a) m = m) → T m = m := by
  first | exact @GlobalTheory.FinWeil.intertwiner_fixes_of_local_vacuum | exact GlobalTheory.FinWeil.intertwiner_fixes_of_local_vacuum | (intros; apply GlobalTheory.FinWeil.intertwiner_fixes_of_local_vacuum <;> assumption)
