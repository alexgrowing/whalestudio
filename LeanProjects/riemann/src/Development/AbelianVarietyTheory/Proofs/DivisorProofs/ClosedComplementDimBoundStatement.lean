import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClosedComplementDimBound
import Mathlib
open CategoryTheory AlgebraicGeometry
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.closed_complement_dim_bound : ∀ (X : Scheme.{0}) (U : X.Opens) (d : ℕ), topologicalKrullDim X = ((d + 1 : ℕ) : WithBot ℕ∞) → (∀ y : X, ringKrullDim (X.presheaf.stalk y) ≤ 1 → y ∈ U) → topologicalKrullDim ((U : Set X)ᶜ : Set X) + 1 ≤ (d : WithBot ℕ∞) := by
  first | exact @GlobalTheory.DimCodim.dim_compl_add_one_le | exact GlobalTheory.DimCodim.dim_compl_add_one_le | (intros; apply GlobalTheory.DimCodim.dim_compl_add_one_le <;> assumption)
