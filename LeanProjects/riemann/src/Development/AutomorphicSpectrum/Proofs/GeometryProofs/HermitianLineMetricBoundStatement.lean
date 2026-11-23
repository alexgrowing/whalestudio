import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.HermitianLineMetricBound
import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LocRatio
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.GrGenOfIsFlagVBOn
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open GlobalTheory.CompanionTheory.Ar.RootHt GroundTheory.Heights₂.Heights

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hermitian_line_metric_bound : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Sp Ω ⟶ X) (K : Type) [Fintype K] (J : K → Type)
    [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (G : Over X) [GrpObj G] [IsCommMonObj G] [Smooth G.hom]
    (Li : Type) [AddCommGroup Li] [Module Ω Li] (M : LieModel G ξ Li) (V : Lat ξ Li) (r : ℕ) (b₀ : Fin r → Li)
    (m : ℕ) (i : Fin r) (e₀ : Ω) (h : LieMetric M y) (A : HermLine J),
    CharZero Ω → (∀ q : X, genPt ξ ⤳ q) → CoordTie ℤ ξ (fun c' : (k : K) → J k => ∏ k, y ⟨k, c' k⟩) → 0 < m →
    LinearIndependent Ω b₀ → Sandwich M V b₀ m → (V.gr b₀ i).IsDegOn Set.univ y A.a e₀ → IsSmoothHerm A →
    ∃ C : ℝ, ∀ (z : Sp ℂ ⟶ X) (w : (Σ k, J k) → ℂ), CoordsAt ξ y z w → ∀ c₀ : (k : K) → J k, (∀ k, w ⟨k, c₀ k⟩ ≠ 0) →
      ∀ (f : Fin i → Li) (e : Li) (v : Fin i → (epsAt z ⟶ G)) (ve : epsAt z ⟶ G) (t : Ω) (u : ℂ),
      (∀ j, f j ∈ flagStep Ω b₀ i) → e ∈ flagStep Ω b₀ (i + 1) → (∀ j, M.ValAt z (f j) (v j)) → M.ValAt z e ve →
      IsCls b₀ i e t → ValAt ξ z (t / gen y A.a e₀ c₀) u → u ≠ 0 → (gramAt h z v).det ≠ 0 →
      |(1 / 2) * (Real.log ‖(gramAt h z (Fin.snoc v ve : Fin (i + 1) → (epsAt z ⟶ G))).det‖ - Real.log ‖(gramAt h z v).det‖) -
        Real.log ‖u‖ - ∑ k, (A.a k : ℝ) * Real.log ‖w ⟨k, c₀ k⟩‖ + Real.log (A.h w)| ≤ C := by
  first | exact @GlobalTheory.CompanionTheory.Ar.RootHt.ArchB.arch_bound | exact GlobalTheory.CompanionTheory.Ar.RootHt.ArchB.arch_bound | (intros; apply GlobalTheory.CompanionTheory.Ar.RootHt.ArchB.arch_bound <;> assumption)
