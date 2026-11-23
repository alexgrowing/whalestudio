import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsGenericWeilPairing
import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GenWeil
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.GlueApplyOfNotInFibre
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsHTFormOver
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_generic_weil_pairing : Out.WeilSt → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (B : Type) [CommRing B] (b : Base l B) (S X : Scheme.{0}) (s : S ⟶ Sp B) (o : Obj D l b s) (t : SAB H X) (f : S ⟶ X) (_ : SABMap o.t t f) (Ω : Type) [Field Ω] [CharZero Ω] (ξ₀ : Sp Ω ⟶ S) (n : ℕ), 1 ≤ n → FullTorsion t.G (ξ₀ ≫ f) n → (∃ ζ : Ω, IsPrimitiveRoot ζ n) → ∃ e, GenWeil t.G t.PP.L (ξ₀ ≫ f) n e := by
  first | exact @GlobalTheory.CompanionTheory.Ar.WeilObj.genWeil_of_obj | exact GlobalTheory.CompanionTheory.Ar.WeilObj.genWeil_of_obj | (intros; apply GlobalTheory.CompanionTheory.Ar.WeilObj.genWeil_of_obj <;> assumption)
