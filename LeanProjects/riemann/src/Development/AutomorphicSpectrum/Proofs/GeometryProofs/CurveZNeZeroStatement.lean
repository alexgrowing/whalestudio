import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.CurveZNeZero
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsCMFrame
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Matrix GlobalTheory GlobalTheory.CM GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.curve_z_ne_zero : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (ρ : ℂ) (Z : Curve0 H ρ), Z.z ≠ 0 := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Fl.curve0_z_ne_zero | exact GlobalTheory.CompanionTheory.Ar.Fl.curve0_z_ne_zero | (intros; apply GlobalTheory.CompanionTheory.Ar.Fl.curve0_z_ne_zero <;> assumption)
