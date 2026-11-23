import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.CharZeroIffNonzeroUnits
import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsSncPatchRat
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.EmbedsGeneric
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.SncBase
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.char_zero_iff_nonzero_units : ∀ (F : Type) [Field F] [NumberField F] (Ω : Type) [Field Ω] [Algebra (𝓞 F) Ω] (X : Scheme.{0}) (ξ : Sp Ω ⟶ X) (κ : Type) (t : κ → Ω), CoordTie (𝓞 F) ξ t → ∀ p : Cpt ξ, Char0 ξ p ↔ ∀ d : 𝓞 F, d ≠ 0 → unitAt ξ p (algebraMap (𝓞 F) Ω d) := by
  first | exact @GlobalTheory.CompanionTheory.Ar.SncBase.CharTie.char_zero_iff_integers_units | exact GlobalTheory.CompanionTheory.Ar.SncBase.CharTie.char_zero_iff_integers_units | (intros; apply GlobalTheory.CompanionTheory.Ar.SncBase.CharTie.char_zero_iff_integers_units <;> assumption)
