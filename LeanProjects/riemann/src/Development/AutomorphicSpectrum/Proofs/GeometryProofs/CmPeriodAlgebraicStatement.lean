import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.CmPeriodAlgebraic
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsCMFrame
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Matrix GlobalTheory GlobalTheory.CM GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_cmPack_field_ge_of_isPeriod : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (FU : FamilyUnif Xo (algebraMap (KA l) ℂ) ty) (i : Fin FU.n) (Z : ∀ b : Bool, Curve0 H (sgnRt H b)) (P : (FU.Di i).La →+ (Fin g → ℂ)) (hP : IsPeriod (FU.Di i) ty P) (n : ℕ) (k : IntermediateField ℚ ℂ), FiniteDimensional ℚ k → 0 < n → (∀ y : (FU.Di i).La, ∃ a ∈ PureType.lat hP (sgnRt H true), ∃ b ∈ PureType.lat hP (sgnRt H false), n • y = a + b) → ∃ X : CMPack Z c FU i hP, k ≤ X.K := by
  first | exact @GlobalTheory.CompanionTheory.Ar.Fl.CMGiven.exists_pack_given | exact GlobalTheory.CompanionTheory.Ar.Fl.CMGiven.exists_pack_given | (intros; apply GlobalTheory.CompanionTheory.Ar.Fl.CMGiven.exists_pack_given <;> assumption)
