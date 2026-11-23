import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AffineOpenExistsFieldPointBasicOpenCommonDenomAl
import Mathlib
open AlgebraicGeometry
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_ringHom_field_common_denom_of_mem_isAffineOpen : ∀ {X : Scheme.{0}} {U : X.Opens} (hU : IsAffineOpen U) (p : X), p ∈ U → ∃ (K : Type) (_ : Field K) (ψ : Γ(X, U) →+* K), (∀ g, ψ g ≠ 0 → p ∈ X.basicOpen g) ∧ ∀ (ι : Type) [Fintype ι] (m : ι → K), ∃ (a : ι → Γ(X, U)) (t : Γ(X, U)), ψ t ≠ 0 ∧ ∀ i, m i * ψ t = ψ (a i) := by
  first | exact @GlobalTheory.affineOpen_exists_field_point_basicOpen_commonDenom | exact GlobalTheory.affineOpen_exists_field_point_basicOpen_commonDenom | (intros; apply GlobalTheory.affineOpen_exists_field_point_basicOpen_commonDenom <;> assumption)
