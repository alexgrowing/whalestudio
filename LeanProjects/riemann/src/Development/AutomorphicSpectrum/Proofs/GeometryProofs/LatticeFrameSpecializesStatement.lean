import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LatticeFrameSpecializes
import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieOmegaLatticeVectorBundle
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieLatticeEvalAtLocalRingStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar Filter Topology Metric

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lattice_frame_specializes : ∀ (X : Scheme.{0}) (G : Over X) [GrpObj G] [IsCommMonObj G] [Smooth G.hom] (Ω : Type) [Field Ω] (ξ : Sp Ω ⟶ X) (E : Type) [AddCommGroup E] [Module Ω E] (M : LieModel G ξ E) (C : Type) [Field C] (z : Sp C ⟶ X) (h : genPt ξ ⤳ centre z) (EC : Type) [AddCommGroup EC] [Module C EC] (N : LieModel G z EC) (g n : ℕ) (b : Fin g → E) (S : Finset (Fin g)) (c : Fin n → E) (L : Lat ξ E) (w : Fin n → EC), IsCptGen ξ → M.lat.IsFrameAt b ⟨centre z, h⟩ → L ⟨centre z, h⟩ = Submodule.span (regAt ξ ⟨centre z, h⟩) (b '' S) → L.IsFrameAt c ⟨centre z, h⟩ → (∀ i, M.ValAt z (c i) (N.pt (w i))) → LinearIndependent C w := by
  first | exact @GlobalTheory.CompanionTheory.Ar.values_frame_sublattice_linearIndependent | exact GlobalTheory.CompanionTheory.Ar.values_frame_sublattice_linearIndependent | (intros; apply GlobalTheory.CompanionTheory.Ar.values_frame_sublattice_linearIndependent <;> assumption)
