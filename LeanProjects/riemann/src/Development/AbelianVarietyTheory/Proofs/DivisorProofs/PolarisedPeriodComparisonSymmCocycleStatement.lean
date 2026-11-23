import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolarisedPeriodComparisonSymmCocycle
import Development.AbelianVarietyTheory.Definitions.Divisors.EvenDefect
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.SiegelToroidalPolCharts
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.SecCmp
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.polarisedPeriod_comparison_symm_cocycle : ∀ (R : Type) [CommRing R] [IsDomain R] (R' : Type) [CommRing R'] [IsDomain R'] (Q : Data R) (ρ : R →+* R') (D : DegPre R') (e : D.X ≃+ Q.X) (f : D.X → D.X → (FractionRing R')ˣ), Function.Injective ρ → Half Q ρ D e f → (∀ a b, f a b = f b a) ∧ ∀ a b c, f (a + b) c * f a b = f a (b + c) * f b c := by
  first | exact @GlobalTheory.PolDeg.half_symm_cocycle | exact GlobalTheory.PolDeg.half_symm_cocycle | (intros; apply GlobalTheory.PolDeg.half_symm_cocycle <;> assumption)
