import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LatticeRegularAtLocalPoint
import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LocRatio
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.GrGenOfIsFlagVBOn
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open GlobalTheory.CompanionTheory.Ar.RootHt GroundTheory.Heights₂.Heights

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lattice_regular_at_local_point : ∀ (X : Scheme.{0}) (G : Over X) [GrpObj G] [IsCommMonObj G] [Smooth G.hom] (Ω : Type) [Field Ω] (ξ : Sp Ω ⟶ X)
    (Li : Type) [AddCommGroup Li] [Module Ω Li] (M : LieModel G ξ Li) (R : Type) [CommRing R] [IsLocalRing R]
    (z : Sp R ⟶ X) (h : genPt ξ ⤳ centre z) (ER : Type) [AddCommGroup ER] [Module R ER] (MR : LieModel G z ER)
    (f : Module.Dual Ω Li), IsCptGen ξ → (∀ e ∈ M.lat ⟨centre z, h⟩, f e ∈ regAt ξ ⟨centre z, h⟩) →
    ∃ g : ER →ₗ[R] R, ∀ (e : Li) (x : ER) (u : R), M.ValAt z e (MR.pt x) → ValAt ξ z (f e) u → g x = u := by
  first | exact @GlobalTheory.CompanionTheory.Ar.RootHt.exists_lieFunctional | exact GlobalTheory.CompanionTheory.Ar.RootHt.exists_lieFunctional | (intros; apply GlobalTheory.CompanionTheory.Ar.RootHt.exists_lieFunctional <;> assumption)
