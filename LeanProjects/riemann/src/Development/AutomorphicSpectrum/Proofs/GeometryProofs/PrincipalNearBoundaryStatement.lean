import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.PrincipalNearBoundary
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.SlopeBoundSt
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ArchBetween
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.BdryChart
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.ClopenCondOnto
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
import Development.AbelianVarietyTheory.PublishedTheorems.SemiabelianTori.GeometricallyConnectedSplitTorusAff
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.principal_near_boundary : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (σ : KA l →+* ℂ) (n a : ℕ) (C : Flat.BdryChart Xo σ n a), 1 ≤ D.p + D.q → σ (baseKA l).ρ = H.rt0 → ∃ ρ K : ℝ, 0 < ρ ∧ ρ ≤ 1 ∧ ∀ z ∈ Metric.ball (0 : Fin n → ℂ) ρ, ∀ P : AbPart C.t (spMap (C.ψ z)), IsPrincipal P.tB ∧ ∀ (Mz : LieModel C.t.G (spMap (C.ψ z)) (Fin C.g → ℂ)), (∀ i, C.M.Lifts (C.ψ z) (𝟙 _) (Pi.single i 1) (Mz.pt (Pi.single i 1))) → ∀ (x : Fin C.g → ℂ) (v : epsAt (𝟙 (Sp ℂ)) ⟶ P.tK.G) (c : ℂ), v.left ≫ P.m.φ = (Mz.pt x).left → HodgeIP P.tB.G P.tB.PP.L (𝟙 _) (v ≫ P.τ.q ≫ P.e.hom) (v ≫ P.τ.q ≫ P.e.hom) c → c.re ≤ K * ∑ i, ‖x i‖ ^ 2 := by
  first | exact @GlobalTheory.CompanionTheory.Ar.QuotLoc.abPart_principal_and_bound | exact GlobalTheory.CompanionTheory.Ar.QuotLoc.abPart_principal_and_bound | (intros; apply GlobalTheory.CompanionTheory.Ar.QuotLoc.abPart_principal_and_bound <;> assumption)
