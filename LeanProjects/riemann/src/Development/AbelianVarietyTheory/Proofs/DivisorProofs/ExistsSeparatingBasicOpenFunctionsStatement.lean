import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSeparatingBasicOpenFunctions
import Mathlib
open AlgebraicGeometry CategoryTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_separating_basicOpen_functions' : ∀ (X : Scheme.{0}) (U : X.Opens), IsAffineOpen U → ∀ (F : Finset X), (∀ a ∈ F, a ∈ U) → (∀ a ∈ F, ∀ b ∈ F, a ⤳ b → a = b) → ∀ W : X → X.Opens, (∀ a ∈ F, a ∈ W a) → ∃ f : X → Γ(X, U), ∀ a ∈ F, a ∈ X.basicOpen (f a) ∧ X.basicOpen (f a) ≤ W a ∧ ∀ b ∈ F, b ≠ a → b ∉ X.basicOpen (f a) := by
  first | exact @GlobalTheory.exists_separating_basicOpen_functions | exact GlobalTheory.exists_separating_basicOpen_functions | (intros; apply GlobalTheory.exists_separating_basicOpen_functions <;> assumption)
