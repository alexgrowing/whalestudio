import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinearUniformisationsCharacterIsoAssociatedCoord
import Development.AbelianVarietyTheory.Definitions.Divisors.SpecializesGenericImage
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsMonoFamNontrivial
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc
open scoped CategoryTheory.Obj
open GlobalTheory.UPoinc Formalism.L2.Pj
open GlobalTheory
open Classical
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.linear_uniformisations_character_iso_associated_coords : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (W : Type) [CommRing W] [IsDomain W]
    [IsLocalRing W], GlobalTheory.Mum.Base W → ∀ (t : SAB H (Sp W)) (P P' : PELUnif (maximalIdeal W) t),
      ∃ e : P.D.toPre.X ≃ₗ[𝓞 E] P'.D.toPre.X, ∀ y r r', PsiCoord P.D.toPre y r → PsiCoord P'.D.toPre (e y) r' →
        Associated (r ^ 2) (r' ^ 2) := by
  first | exact @GlobalTheory.PelUnifUniqCoord.main | exact GlobalTheory.PelUnifUniqCoord.main | (intros; apply GlobalTheory.PelUnifUniqCoord.main <;> assumption)
