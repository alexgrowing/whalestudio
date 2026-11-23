import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AffineSpaceSmoothNormal
import Mathlib
open CategoryTheory AlgebraicGeometry
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.affine_space_smooth_normal : ∀ (X : Scheme.{0}) (K : Type) [Field K] (s : X ⟶ Spec (.of K)), Smooth s → ∀ (V : X.Opens), IsAffineOpen V → IsIntegral V.toScheme → ∀ (ι : Type) [Finite ι], Smooth ((𝔸(ι; V.toScheme) ↘ V.toScheme) ≫ V.ι) ∧ LocallyOfFiniteType ((𝔸(ι; V.toScheme) ↘ V.toScheme) ≫ V.ι) ∧ IsIntegral 𝔸(ι; V.toScheme) ∧ ∀ t : 𝔸(ι; V.toScheme), IsIntegrallyClosed (𝔸(ι; V.toScheme).presheaf.stalk t) := by
  first | exact @GlobalTheory.affineSpace_over_integral_affine_open_smooth_integral_normal | exact GlobalTheory.affineSpace_over_integral_affine_open_smooth_integral_normal | (intros; apply GlobalTheory.affineSpace_over_integral_affine_open_smooth_integral_normal <;> assumption)
