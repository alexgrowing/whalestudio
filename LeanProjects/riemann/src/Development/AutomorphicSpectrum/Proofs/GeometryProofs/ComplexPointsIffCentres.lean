import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsGenericFlag
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.FrameDefinitions.Metric
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LocalRingPointsExistsUniqueStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar

theorem mem_mcPts_iff_exists_coordsAt : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω), CoordTie ℤ ξ (fun c' : (k : K) → J k => ∏ k, y ⟨k, c' k⟩) → ∀ w : (Σ k, J k) → ℂ, w ∈ mcPts (mCoordIdeal y) ↔ ∃ z : Spec (CommRingCat.of ℂ) ⟶ X, genPt ξ ⤳ centre z ∧ CoordsAt ξ y z w := by
  intro X Ω _ ξ K _ J _ y tie w
  have key := GlobalTheory.T.local_ring_points_existsUnique X Ω ξ K J y tie ℂ
  have hval : ∀ g : MvPolynomial (Σ k, J k) ℤ,
      MvPolynomial.aeval w g = MvPolynomial.eval w (MvPolynomial.map (Int.castRingHom ℂ) g) := by
    intro g
    rw [MvPolynomial.eval_map, MvPolynomial.aeval_def]
    congr 1
  constructor
  · rintro ⟨hne, hvan⟩
    obtain ⟨z, ⟨hz, hc⟩, -⟩ := key.1 w
      (fun k => (hne k).imp fun _ h => isUnit_iff_ne_zero.mpr h)
      (fun g hg => by rw [hval]; exact hvan g hg)
    exact ⟨z, hz, hc⟩
  · rintro ⟨z, hz, hc⟩
    refine ⟨fun k => (hc.1 k).imp fun _ h => h.ne_zero, fun f hf => ?_⟩
    rw [← hval]
    exact (key.2.2 z w hz hc).1 f hf

end GlobalTheory.CompanionTheory.Ar
