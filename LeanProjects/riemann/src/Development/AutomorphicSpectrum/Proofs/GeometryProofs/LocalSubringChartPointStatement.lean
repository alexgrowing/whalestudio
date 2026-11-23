import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LocalSubringChartPoint
import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.CoordsAt
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.PrimeChartExistsUniquePointStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.RegAtIffChartLocalization
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsUniqueCentreLocalHomStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsExcisionNbhdAway
open AlgebraicGeometry CategoryTheory Limits GlobalTheory.CompanionTheory.Ar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_subring_chart_point : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (κ : Type) (x : κ → Ω) (c : κ), CoordTie ℤ ξ x → x c ≠ 0 → ∀ (F : Type) [Field F] (θ : Ω →+* F) (A : Subring F) [IsLocalRing A], (∀ j, θ (x j / x c) ∈ A) → ∃ (z : Spec (CommRingCat.of A) ⟶ X) (h : genPt ξ ⤳ centre z), InChart ξ x c ⟨centre z, h⟩ ∧ (∀ s : X.presheaf.stalk (centre z), (((Scheme.stalkClosedPointTo z).hom s : A) : F) = θ (genMap ξ ⟨centre z, h⟩ s)) ∧ Spec.map (CommRingCat.ofHom A.subtype) ≫ z = Spec.map (CommRingCat.ofHom θ) ≫ ξ := by
  first | exact @GlobalTheory.CompanionTheory.Ar.ChartPoint.point_of_local_subring | exact GlobalTheory.CompanionTheory.Ar.ChartPoint.point_of_local_subring | (intros; apply GlobalTheory.CompanionTheory.Ar.ChartPoint.point_of_local_subring <;> assumption)
