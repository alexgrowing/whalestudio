import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteMapClosedFibre
import Mathlib
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.IsFiniteLengthOfIsArtinianRingAnnihilator
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace
open GlobalTheory GlobalTheory.QCoh
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.finite_map_closed_fibre : ∀ {X Y : Scheme.{0}} (f : Y ⟶ X) (V : X.Opens), IsAffineOpen V → IsAffineOpen (f ⁻¹ᵁ V) → (letI := (f.app V).hom.toAlgebra; Module.Finite Γ(X, V) Γ(Y, f ⁻¹ᵁ V)) → ∀ (x : X), x ∈ V → IsClosed ({x} : Set X) → (f.base ⁻¹' {x}).Finite ∧ ∀ y : Y, f.base y = x → IsClosed ({y} : Set Y) := by
  first | exact @GlobalTheory.fibre_finite_isClosed_of_affine_finite | exact GlobalTheory.fibre_finite_isClosed_of_affine_finite | (intros; apply GlobalTheory.fibre_finite_isClosed_of_affine_finite <;> assumption)
