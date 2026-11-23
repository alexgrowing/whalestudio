import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HodgeCorrespondenceSurjective
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HodgeIntoDeRhamInjectiveImports
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExactAndSurjectiveAppOfExactOfEpi
open CategoryTheory AlgebraicGeometry Limits ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.DeRham GlobalTheory.DeRhamSheaf GlobalTheory.LieVB
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.hodge_correspondence_surjective : GlobalTheory.CovTop.Hypotheses2 → ∀ (T : Scheme.{0}) (A : Over T) [GrpObj A] (g : ℕ),
    IsAbelianScheme A → SmoothOfRelativeDimension g A.hom →
    ∀ (V : T.Opens) (hV : IsAffineOpen V) (c : primDR (onAff A hV)), c ∈ PrimitiveSubmodule (onAff A hV) →
      ∃ s, GlobalTheory.HodgeSub.Corr A hV s c := by
  first | exact @GlobalTheory.HodgeSubSurj.main | exact GlobalTheory.HodgeSubSurj.main | (intros; apply GlobalTheory.HodgeSubSurj.main <;> assumption)
