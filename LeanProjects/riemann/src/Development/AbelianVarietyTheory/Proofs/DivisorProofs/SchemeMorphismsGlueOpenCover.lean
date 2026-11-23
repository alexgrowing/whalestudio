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

namespace GlobalTheory

open CategoryTheory.Limits

theorem glue_homs_of_opens_cover {X Y : Scheme.{0}} {κ : Type} (U : κ → X.Opens) (hU : ⨆ k, U k = ⊤)
    (f : ∀ k, (U k).toScheme ⟶ Y)
    (hf : ∀ k l, X.homOfLE (inf_le_left : U k ⊓ U l ≤ U k) ≫ f k =
      X.homOfLE (inf_le_right : U k ⊓ U l ≤ U l) ≫ f l) :
    ∃ g : X ⟶ Y, ∀ k, (U k).ι ≫ g = f k := by
  let 𝒰 := X.openCoverOfIsOpenCover U hU
  have hc : ∀ a b, pullback.fst (U a).ι (U b).ι ≫ f a = pullback.snd (U a).ι (U b).ι ≫ f b := by
    intro a b
    have P := isPullback_opens_inf (U a) (U b)
    rw [← cancel_epi P.isoPullback.hom, IsPullback.isoPullback_hom_fst_assoc,
      IsPullback.isoPullback_hom_snd_assoc]
    exact hf a b
  exact ⟨𝒰.glueMorphisms f hc, fun k => 𝒰.ι_glueMorphisms f hc k⟩

end GlobalTheory
