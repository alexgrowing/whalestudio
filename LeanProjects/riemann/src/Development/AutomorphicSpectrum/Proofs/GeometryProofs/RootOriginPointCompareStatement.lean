import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.RootOriginPointCompare
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.GoodOrigin
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.SlopeBoundSt
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ArchBetween
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IntegralClosureHeightEqOneOfLiesOver
import Development.AutomorphicSpectrum.Statements.GeometryStatements.FlatLineGenerator
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.JoinModelPointsProjectStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.RootModelFlagCompareStatement
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.HasMultiplierLine
open AlgebraicGeometry CategoryTheory NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.root_origin_point_compare : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S S₀ : Finset ℕ) (M R : Top.RootModel (CMType H) (D.p + D.q)) (Sys : PB.AnSys (Top.dimFl (CMType H) (D.p + D.q)) (Option (RootIx D))) (Fx : FixedData Y Sys) (o : RootOrigin Y S M Fx) (o₀ : RootOrigin Y S₀ R Fx) (x : o.Re.R.X) (x' : o₀.Re.R.X) (w₁ : (Σ k, M.ι k) → ℂ) (w₂ : (Σ k, R.ι k) → ℂ) (v : RootIx D → ℝ) (t : ℝ), 0 < t → t ≤ Sys.t₀ → w₁ ∈ mcPts M.P → w₂ ∈ mcPts R.P → ReciprocityTheory.ChartRestriction.G.Geo.SameOrbit (o.Re.R.lift x x) w₁ → ReciprocityTheory.ChartRestriction.G.Geo.SameOrbit (o₀.Re.R.lift x' x') w₂ → o.Re.π x = o₀.Re.π x' → o.Re.π x ∈ Sys.open' → (∀ r, 0 < v r ∧ v r * (o₀.sing r).h w₂ = (o.sing r).h w₁) → ∀ (τ : CMType H) (p : Fin (D.p + D.q)), -∑ k ∈ Finset.Iic p, (Real.log ((M.x t (τ, k)).h w₁) - Real.log ((R.x 1 (τ, k)).h w₂) - Real.log (v (τ, k))) = Sys.phT (some (τ, p)) t (o.Re.π x) + (Real.log ((o₀.Re.ref (some (τ, p))).h w₂) + ∑ k ∈ Finset.Iic p, Real.log ((R.x 1 (τ, k)).h w₂)) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.OrArch.defect_eq_regWeight_add_bracket | exact GlobalTheory.CompanionTheory.Ar.OrArch.defect_eq_regWeight_add_bracket | (intros; apply GlobalTheory.CompanionTheory.Ar.OrArch.defect_eq_regWeight_add_bracket <;> assumption)
