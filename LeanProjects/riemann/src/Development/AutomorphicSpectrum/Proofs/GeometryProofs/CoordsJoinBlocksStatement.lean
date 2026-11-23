import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.CoordsJoinBlocks
import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsGenericFlag
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.FrameDefinitions.Metric
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.coords_join_blocks : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (K' : Type) [Fintype K'] (J' : K' → Type) [∀ k, Fintype (J' k)] (s : (Σ k, J' k) → Ω), CoordTie ℤ ξ (fun c' : (k : K) → J k => ∏ k, y ⟨k, c' k⟩) → (∀ (k : K') (p : Cpt ξ), ∃ i, InChart ξ (fun i' : J' k => s ⟨k, i'⟩) i p) → CoordTie ℤ ξ fun c' : (k : K ⊕ K') → Sum.elim J J' k => (∏ k, y ⟨k, c' (Sum.inl k)⟩) * ∏ k, s ⟨k, c' (Sum.inr k)⟩ := by
  first | exact @GlobalTheory.CompanionTheory.Ar.AddBlockMulti.add_block_multi | exact GlobalTheory.CompanionTheory.Ar.AddBlockMulti.add_block_multi | (intros; apply GlobalTheory.CompanionTheory.Ar.AddBlockMulti.add_block_multi <;> assumption)
