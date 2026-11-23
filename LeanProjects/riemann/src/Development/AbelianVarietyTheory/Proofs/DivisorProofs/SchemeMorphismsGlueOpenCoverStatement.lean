import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchemeMorphismsGlueOpenCover
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsFlagBundleRankOne
import Development.AbelianVarietyTheory.Definitions.Divisors.NormSqColGrLineOfOrthogonal
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.RegularAlteration
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ArBirational
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.RestrictPullbackIsoHomAppPullbackSections
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ColSec
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ColSecOn
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.VB GlobalTheory.FlagZ GlobalTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.scheme_morphisms_glue_open_cover : ∀ {X Y : Scheme.{0}} {κ : Type} (U : κ → X.Opens), ⨆ k, U k = ⊤ → ∀ (f : ∀ k, (U k).toScheme ⟶ Y),
    (∀ k l, X.homOfLE (inf_le_left : U k ⊓ U l ≤ U k) ≫ f k = X.homOfLE (inf_le_right : U k ⊓ U l ≤ U l) ≫ f l) →
    ∃ g : X ⟶ Y, ∀ k, (U k).ι ≫ g = f k := by
  first | exact @GlobalTheory.glue_homs_of_opens_cover | exact GlobalTheory.glue_homs_of_opens_cover | (intros; apply GlobalTheory.glue_homs_of_opens_cover <;> assumption)
