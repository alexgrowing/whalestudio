import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsPeriodAtRestrict
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.EmbedsGeneric
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.GoodOrigin
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IntegralClosureHeightEqOneOfLiesOver
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.PotentialsBoundedRegSettingEqReference
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ComplexPointsIffCentresStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HodgeCptFlagXdeg
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.CoordsAtSmul
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GroundTheory.Heights₂.Heights.LowerBoundFree

namespace GlobalTheory.CompanionTheory.Ar.BdSym

theorem boundary_closed_torus_conj : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (T : Set X) (bd : Ideal (MRing J)), CoordTie ℤ ξ (fun c' : (k : K) → J k => ∏ k, y ⟨k, c' k⟩) → (∀ (z : Spec (CommRingCat.of ℂ) ⟶ X) w, CoordsAt ξ y z w → (w ∈ mcPts bd ↔ centre z ∉ T)) → IsClosed ((↑) ⁻¹' (mcPts (mCoordIdeal y) ∩ mcPts bd) : Set (mcPts (mCoordIdeal y))) ∧ (∀ z ∈ mcPts (mCoordIdeal y) ∩ mcPts bd, ∀ c : K → ℂ, (∀ k, c k ≠ 0) → torusSmul c z ∈ mcPts (mCoordIdeal y) ∩ mcPts bd) ∧ ∀ z ∈ mcPts (mCoordIdeal y) ∩ mcPts bd, conjVec z ∈ mcPts (mCoordIdeal y) ∩ mcPts bd := by
  intro X Ω _ ξ K _ J _ y T bd hT hbd
  have key := GlobalTheory.T.complex_points_iff_centres X Ω ξ K J y hT
  refine ⟨?_, ?_, ?_⟩
  · have e : ((↑) ⁻¹' (mcPts (mCoordIdeal y) ∩ mcPts bd) : Set (mcPts (mCoordIdeal y))) =
        ⋂ f ∈ bd, {w : mcPts (mCoordIdeal y) |
          MvPolynomial.eval w.1 (MvPolynomial.map (Int.castRingHom ℂ) f) = 0} := by
      ext w
      have hw : w.1 ∈ mcPts (mCoordIdeal y) := w.2
      rw [Set.mem_iInter₂]
      simp only [mcPts, Set.mem_preimage, Set.mem_inter_iff, Set.mem_ofPred_eq] at hw ⊢
      exact ⟨fun h => h.2.2, fun h => ⟨hw, hw.1, h⟩⟩
    rw [e]
    refine isClosed_iInter fun f => isClosed_iInter fun _ => isClosed_eq ?_ continuous_const
    exact (MvPolynomial.continuous_eval _).comp continuous_subtype_val
  · rintro w ⟨hw1, hw2⟩ c hc
    obtain ⟨z, hz, hzw⟩ := (key w).1 hw1
    have hzc : CoordsAt ξ y z (torusSmul c w) := by
      have h' := hzw
      unfold CoordsAt at h' ⊢
      refine ⟨fun k => ?_, fun k i hu => ?_⟩
      · obtain ⟨i, hi⟩ := h'.1 k
        refine ⟨i, isUnit_iff_ne_zero.2 ?_⟩
        show c k * w ⟨k, i⟩ ≠ 0
        exact mul_ne_zero (hc k) (isUnit_iff_ne_zero.1 hi)
      · have hu' : IsUnit (w ⟨k, i⟩) := by
          refine isUnit_iff_ne_zero.2 fun h0 => isUnit_iff_ne_zero.1 hu ?_
          show c k * w ⟨k, i⟩ = 0
          rw [h0, mul_zero]
        obtain ⟨hy, hr⟩ := h'.2 k i hu'
        refine ⟨hy, fun j => ?_⟩
        obtain ⟨r, hr1, hr2⟩ := hr j
        refine ⟨r, hr1, ?_⟩
        show c k * w ⟨k, j⟩ = r * (c k * w ⟨k, i⟩)
        rw [hr2]
        ring
    exact Set.mem_inter ((key _).2 ⟨z, hz, hzc⟩) ((hbd z _ hzc).2 ((hbd z w hzw).1 hw2))
  · rintro w ⟨hw1, hw2⟩
    obtain ⟨z, hz, hzw⟩ := (key w).1 hw1
    have hzc := GlobalTheory.CompanionTheory.Ar.HodgeLine.coordsAt_conj hzw
    have hcz : centre (GlobalTheory.CompanionTheory.Ar.HodgeLine.cj z) = centre z := GlobalTheory.CompanionTheory.Ar.HodgeLine.centre_cj z
    have hz' : GlobalTheory.CompanionTheory.Ar.genPt ξ ⤳ centre (GlobalTheory.CompanionTheory.Ar.HodgeLine.cj z) := by
      rw [hcz]
      exact hz
    have hT' : centre (GlobalTheory.CompanionTheory.Ar.HodgeLine.cj z) ∉ T := by
      rw [hcz]
      exact (hbd z w hzw).1 hw2
    exact Set.mem_inter ((key (conjVec w)).2 ⟨GlobalTheory.CompanionTheory.Ar.HodgeLine.cj z, hz', hzc⟩) ((hbd _ _ hzc).2 hT')

end GlobalTheory.CompanionTheory.Ar.BdSym
