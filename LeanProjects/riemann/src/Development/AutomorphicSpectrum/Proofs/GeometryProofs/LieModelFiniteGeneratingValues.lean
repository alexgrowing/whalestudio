import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.AbBound
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieOmegaLatticeVectorBundle
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.CoordinateIdeals
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.QuotUnif Metric

namespace GlobalTheory.CompanionTheory.Ar.QuotUnif

set_option backward.isDefEq.respectTransparency false in

theorem lie_frame_values_basis : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Sp Ω ⟶ X) (G : Over X) [GrpObj G] [IsCommMonObj G] [Smooth G.hom] (Li : Type) [AddCommGroup Li] [Module Ω Li] (M : LieModel G ξ Li) (z₀ : Sp ℂ ⟶ X), IsCptGen ξ → genPt ξ ⤳ centre z₀ → ∃ (N : ℕ) (s : Fin N → Li), (∀ i, ∃ v : epsAt z₀ ⟶ G, M.ValAt z₀ (s i) v) ∧ ∀ (V : Type) [AddCommGroup V] [Module ℂ V] (Mz : LieModel G z₀ V) (b : Fin N → V), (∀ i, M.ValAt z₀ (s i) (Mz.pt (b i))) → LinearIndependent ℂ b ∧ Submodule.span ℂ (Set.range b) = ⊤ := by
  intro X Ω _ ξ G _ _ _ Li _ _ M z₀ hξ h
  obtain ⟨R, _, x, hx, F, _, _, MR, n, b₀, hp⟩ := LieVB.exists_chart G (centre z₀)
  have hq' : (X.fromSpecStalk (centre z₀)) (IsLocalRing.closedPoint (X.presheaf.stalk (centre z₀))) ∈
      x.opensRange := by
    rw [Scheme.fromSpecStalk_closedPoint]
    exact hp
  obtain ⟨ψ, hψ⟩ := LieVB.exists_lift (A := X.presheaf.stalk (centre z₀)) x (X.fromSpecStalk (centre z₀)) hq'
  obtain ⟨EA, _, _, ⟨MA⟩⟩ := lieModel_exists X G (X.presheaf.stalk (centre z₀)) (X.fromSpecStalk (centre z₀))
  obtain ⟨-, BA, -, -⟩ := LieVB.basis_tr (A := X.presheaf.stalk (centre z₀)) ψ x (X.fromSpecStalk (centre z₀))
    hψ MR MA b₀
  obtain ⟨i, hi⟩ := LieVB.exists_tr (A := X.presheaf.stalk (centre z₀)) (X.fromSpecStalk (centre z₀)) ξ
    (genMap ξ ⟨centre z₀, h⟩) (LieTangent.spec_genMap ξ ⟨centre z₀, h⟩) MA M
  have hext : ∀ a, M.Extends ⟨centre z₀, h⟩ (i a) (MA.pt a) := fun a => ⟨MA.tan a, hi a⟩
  refine ⟨n, fun k => i (BA k), fun k => ?_, fun V _ _ Mz b hb => ?_⟩
  · obtain ⟨E₀, _, _, ⟨M₀⟩⟩ := lieModel_exists X G ℂ z₀
    obtain ⟨j, hj⟩ := LieVB.exists_tr (A := X.presheaf.stalk (centre z₀)) (X.fromSpecStalk (centre z₀)) z₀
      (Scheme.stalkClosedPointTo z₀).hom (LieTangent.spec_centre z₀) MA M₀
    exact ⟨M₀.pt (j (BA k)), h, _, hext _, hj _⟩
  · obtain ⟨β, B, hB, hβ⟩ := LieVB.basis_tr (R := X.presheaf.stalk (centre z₀))
      (Scheme.stalkClosedPointTo z₀).hom (X.fromSpecStalk (centre z₀)) z₀ (LieTangent.spec_centre z₀) MA Mz BA
    have hbB : b = B := by
      funext k
      obtain ⟨_, v, hv, hw⟩ := hb k
      have hva : MA.pt (BA k) = v := (hext (BA k)).unique (hξ.inj _) hv
      subst hva
      rw [hB]
      exact LieVB.pt_left_inj Mz (hw.trans (hβ _).symm)
    rw [hbB]
    exact ⟨B.linearIndependent, B.span_eq⟩

end GlobalTheory.CompanionTheory.Ar.QuotUnif
