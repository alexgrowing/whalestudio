import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.SumLatticeWedgeComap
import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.BdryChart
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.IsPshLocallyIntegrableStatement
import Development.AutomorphicSpectrum.Statements.GeometryStatements.FlatDegree
import Development.AutomorphicSpectrum.Statements.GeometryStatements.NineGeoU
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.is_frame_at_tail_of_is_frame_at_comap_sup_lattice : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (P Wv : Type) [AddCommGroup P] [Module Ω P] [AddCommGroup Wv] [Module Ω Wv] (i : Wv →ₗ[Ω] P) (A B : Lat ξ P) (Va Vb : Submodule Ω P) (N j : ℕ) (hj : j ≤ N) (b : Fin N → Wv) (s : Fin (N - j) → P) (p : Cpt ξ), Function.Injective i → LinearMap.range i = Va ⊔ Vb → Disjoint Va Vb → (∀ x ∈ A p, x ∈ Va) → (∀ x ∈ B p, x ∈ Vb) → (Lat.comap (fun q => A q ⊔ B q) i).IsFrameAt b p → Submodule.span Ω (Set.range (b ∘ headIdx hj)) = Va.comap i → (∀ k, s k ∈ Vb ∧ i (b (tailIdx hj k)) - s k ∈ Va) → B.IsFrameAt s p ∧ (∀ k, i (b (tailIdx hj k)) - s k ∈ A p) ∧ ∀ k, i (b (headIdx hj k)) ∈ A p := by
  first | exact @GlobalTheory.CompanionTheory.Ar.BlockFrame.frame_of_sum_frame | exact GlobalTheory.CompanionTheory.Ar.BlockFrame.frame_of_sum_frame | (intros; apply GlobalTheory.CompanionTheory.Ar.BlockFrame.frame_of_sum_frame <;> assumption)
