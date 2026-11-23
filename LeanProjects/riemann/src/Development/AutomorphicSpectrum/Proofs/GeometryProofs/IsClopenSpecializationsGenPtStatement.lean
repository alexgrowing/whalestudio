import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsClopenSpecializationsGenPt
import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsCptGen
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.CompanionTheory.Ar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isClopen_specializations_genPt : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) [IsLocallyNoetherian X], IsCptGen ξ → IsClopen {q : X | genPt ξ ⤳ q} := by
  first | exact @GlobalTheory.CompanionTheory.Ar.isClopen_setOf_genPt_specializes | exact GlobalTheory.CompanionTheory.Ar.isClopen_setOf_genPt_specializes | (intros; apply GlobalTheory.CompanionTheory.Ar.isClopen_setOf_genPt_specializes <;> assumption)
