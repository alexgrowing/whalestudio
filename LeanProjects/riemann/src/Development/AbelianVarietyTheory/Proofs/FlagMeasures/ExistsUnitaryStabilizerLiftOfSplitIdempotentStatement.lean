import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsUnitaryStabilizerLiftOfSplitIdempotent
import Formalism.SharpRestriction.CuspSpanNormBounds.GlobAut
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ExistsReduction
open MeasureTheory Formalism.MainNotions.S GlobalTheory.RowLev NumberField IsDedekindDomain Matrix
open scoped InnerProductSpace ComplexOrder TensorProduct Pointwise Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_unitary_stabilizer_lift_of_split_idempotent : ∀ (A : Type) [CommRing A] (s : A →+* A) (S : Subring A) (n : ℕ) (J : Matrix (Fin n) (Fin n) A) (Λ : Submodule S (Fin n → A)) (k : Type) [Field k] (r : S →+* k) (c : Λ →ₛₗ[r] (Fin n → k)) (ε : S), (∀ a, s (s a) = a) → (∀ a ∈ S, s a ∈ S) → Formalism.UG.IsHerm s J → IsUnit J.det → Λ.FG → Submodule.span A (Λ : Set (Fin n → A)) = ⊤ → (∀ y, y ∈ Λ ↔ ∀ y' ∈ Λ, Formalism.UG.hform s J y' y ∈ S) → ε * ε = ε → (ε : A) * s ε = 0 → r ε = 1 → Function.Surjective r → (∀ z : S, r z ≠ 0 → ∃ t : S, z * t * ε = ε) → Function.Surjective c → (∀ y : Λ, c y = 0 → (y : Fin n → A) ∈ RingHom.ker r • Λ) → ∀ M : GL (Fin n) k, ∃ x : GL (Fin n) A, x ∈ Formalism.UG.UJ s J ∧ x ∈ Formalism.UG.stabGL Λ ∧ (∀ (y : Λ) (h : (x : Matrix (Fin n) (Fin n) A) *ᵥ (y : Fin n → A) ∈ Λ), c ⟨_, h⟩ = (M : Matrix (Fin n) (Fin n) k) *ᵥ c y) ∧ ∀ y ∈ Λ, ∃ z ∈ Λ, ((x : Matrix (Fin n) (Fin n) A) - 1) *ᵥ y = ((ε : A) + s ε) • z := by
  first | exact @GlobalTheory.SplitLift.exists_unitary_lift | exact GlobalTheory.SplitLift.exists_unitary_lift | (intros; apply GlobalTheory.SplitLift.exists_unitary_lift <;> assumption)
