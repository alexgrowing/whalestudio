import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ResidueFieldBaseChangePullback
import Mathlib
open AlgebraicGeometry CategoryTheory Limits
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.residue_field_base_change_pullback : ∀ (K K' : Type) [Field K] [Field K'] [Algebra K K'] (X X' : AlgebraicGeometry.Scheme.{0}) (g : X ⟶ AlgebraicGeometry.Spec (CommRingCat.of K)) (p : X' ⟶ X) (g' : X' ⟶ AlgebraicGeometry.Spec (CommRingCat.of K')), CategoryTheory.IsPullback p g' g (AlgebraicGeometry.Spec.map (CommRingCat.ofHom (algebraMap K K'))) → ∀ x : X, (letI : Algebra K (X.residueField x) := (AlgebraicGeometry.Spec.preimage (X.fromSpecResidueField x ≫ g)).hom.toAlgebra; IsDomain (TensorProduct K (X.residueField x) K')) → IsPreirreducible ((⇑p) ⁻¹' {x}) := by
  first | exact @GlobalTheory.baseChange_field_fibre_isPreirreducible | exact GlobalTheory.baseChange_field_fibre_isPreirreducible | (intros; apply GlobalTheory.baseChange_field_fibre_isPreirreducible <;> assumption)
