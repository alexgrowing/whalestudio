import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AffineVectorBundleSectionSeparation
import Mathlib
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.RestrictPullbackIsoHomAppPullbackSections
import Development.AbelianVarietyTheory.Definitions.Divisors.ToBidualNaturalityDualSheafTranspose
open CategoryTheory AlgebraicGeometry
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.affine_vector_bundle_section_separation : ∀ (X : Scheme.{0}) [IsAffine X] (F : X.Modules) (r : ℕ), GlobalTheory.VB.IsVB F r →
    ∀ z : Γ(F, ⊤), (∀ L : F ⟶ GlobalTheory.structureModule X, L.app ⊤ z = 0) → z = 0 := by
  first | exact @GlobalTheory.VB.eq_zero_of_forall_hom_app_eq_zero | exact GlobalTheory.VB.eq_zero_of_forall_hom_app_eq_zero | (intros; apply GlobalTheory.VB.eq_zero_of_forall_hom_app_eq_zero <;> assumption)
