import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ComplexPointsClosureCoords
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LocRatio
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.GrGenOfIsFlagVBOn
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.CoordsAtSmul
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open GlobalTheory.CompanionTheory.Ar.RootHt GroundTheory.Heights₂.Heights

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.complex_points_closure_coords : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Sp Ω ⟶ X) (K : Type) [Fintype K] (J : K → Type)
    [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω),
    (∀ q : X, genPt ξ ⤳ q) → CoordTie ℤ ξ (fun c' : (k : K) → J k => ∏ k, y ⟨k, c' k⟩) →
    ∀ w : (Σ k, J k) → ℂ, w ∈ closure {w' : (Σ k, J k) → ℂ | ∃ z : Sp ℂ ⟶ X, CoordsAt ξ y z w'} →
      (∀ k, ∃ i, w ⟨k, i⟩ ≠ 0) → ∃ z : Sp ℂ ⟶ X, CoordsAt ξ y z w := by
  first | exact @GlobalTheory.CompanionTheory.Ar.RootHt.ArchC.closed_coords' | exact GlobalTheory.CompanionTheory.Ar.RootHt.ArchC.closed_coords' | (intros; apply GlobalTheory.CompanionTheory.Ar.RootHt.ArchC.closed_coords' <;> assumption)
