import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieMetricFrameProjectionAt
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LocRatio
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.GrGenOfIsFlagVBOn
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.CoordsAtSmul
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsLieModel
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieLatticeEvalAtLocalRingStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open GlobalTheory.CompanionTheory.Ar.RootHt GroundTheory.Heights₂.Heights

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lie_metric_frame_projection_at : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Sp Ω ⟶ X) (K : Type) (J : K → Type)
    (y : (Σ k, J k) → Ω) (G : Over X) [GrpObj G] [IsCommMonObj G] [Smooth G.hom]
    (Li : Type) [AddCommGroup Li] [Module Ω Li] (M : LieModel G ξ Li) (h : LieMetric M y) (z : Sp ℂ ⟶ X)
    (hz : genPt ξ ⤳ centre z) (r : ℕ) (b : Fin r → Li) (π : Fin r → Module.Dual Ω Li)
    (B : Fin r → (epsAt z ⟶ G)) (i : Fin r), IsCptGen ξ → (∀ j l, π j (b l) = if j = l then 1 else 0) →
    (∀ j, ∀ e ∈ M.lat ⟨centre z, hz⟩, π j e ∈ regAt ξ ⟨centre z, hz⟩) → (∀ j, M.ValAt z (b j) (B j)) →
    ∀ (f : Fin i → Li) (e : Li) (v : Fin i → (epsAt z ⟶ G)) (ve : epsAt z ⟶ G) (s : ℂ),
      (∀ j, f j ∈ flagStep Ω b i) → e ∈ flagStep Ω b (i + 1) → (∀ j, M.ValAt z (f j) (v j)) → M.ValAt z e ve →
      ValAt ξ z (π i e) s → s ≠ 0 → (gramAt h z v).det ≠ 0 →
      (1 / 2) * (Real.log ‖(gramAt h z (Fin.snoc v ve : Fin (i + 1) → (epsAt z ⟶ G))).det‖ -
          Real.log ‖(gramAt h z v).det‖) =
        Real.log ‖s‖ + (1 / 2) * (Real.log ‖(gramAt h z fun l : Fin (i + 1) => B (Fin.castLE i.2 l)).det‖ -
          Real.log ‖(gramAt h z fun l : Fin i => B (Fin.castLE i.2.le l)).det‖) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.RootHt.ArchB.gram_val | exact GlobalTheory.CompanionTheory.Ar.RootHt.ArchB.gram_val | (intros; apply GlobalTheory.CompanionTheory.Ar.RootHt.ArchB.gram_val <;> assumption)
