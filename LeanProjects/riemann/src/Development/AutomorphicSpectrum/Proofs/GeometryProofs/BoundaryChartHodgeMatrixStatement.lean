import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.BoundaryChartHodgeMatrix
import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.BdryChart
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsFlatAnIffIsConstMul
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.LevelSectionsExactKernelLocusOpen
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.ClopenCondOnto
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat Filter Topology Metric
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.boundary_chart_hodge_matrix : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (σ : KA l →+* ℂ) (n a : ℕ) (C : BdryChart Xo σ n a) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (FU : FamilyUnif Xo σ ty) (ρ : ℝ) (e : FamExp C.t.G C.M (ball 0 ρ) C.ψ), 0 < ρ → ρ ≤ 1 → ∃ (i : Fin FU.n) (Hf : (Fin n → ℂ) → Matrix (Fin C.g) (Fin C.g) ℂ), Module.finrank ℤ (FU.Di i).La = 2 * C.g ∧ (∀ z ∈ punct n a ρ, (Hf z).IsHermitian ∧ (∀ x : Fin C.g → ℂ, x ≠ 0 → 0 < (hermForm (Hf z) x x).re) ∧ C.IsRiem z (Hf z) ∧ ∀ (N : ℕ) (ζ : ℂˣ), 0 < N → ∀ x ∈ e.per z, ∀ x' ∈ e.per z, GlobalTheory.UU.CubWeil C.t.cub N (e.ex z ((N : ℂ)⁻¹ • x)) (e.ex z ((N : ℂ)⁻¹ • x')) (unitOn ζ) → (ζ : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * ((hermForm (Hf z) x x').im : ℂ) / N)) ∧ ∀ z₀ ∈ punct n a ρ, ∃ N : Set (Fin n → ℂ), IsOpen N ∧ z₀ ∈ N ∧ N ⊆ punct n a ρ ∧ ∃ P : (Fin n → ℂ) → ((FU.Di i).La →+ (Fin C.g → ℂ)), (∀ x, DifferentiableOn ℂ (fun z => P z x) N) ∧ ∀ z ∈ N, Function.Injective (P z) ∧ ((P z).range : Set (Fin C.g → ℂ)) = e.per z ∧ ∀ x y, (hermForm (Hf z) (P z x) (P z y)).im = (FU.Di i).EF x y := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Flat.exists_marking | exact GlobalTheory.CompanionTheory.Ar.Flat.exists_marking | (intros; apply GlobalTheory.CompanionTheory.Ar.Flat.exists_marking <;> assumption)
