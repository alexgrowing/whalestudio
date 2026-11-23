import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TateUnramifiedOfTorsionUnramified
import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverMorphismRestrictOfRelAmple
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.TwistingSheafOneChartEqPreimageStandardChart
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsRegularFnIffOfIsAffineOpen
import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.BijectiveSmulChartSec
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing

noncomputable section

open CategoryTheory Limits AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.SectionLattice

def IntegralAtSection {W K' : Type} [CommRing W] [Field K'] [Algebra W K'] {G : Scheme.{0}}
    (p : G ⟶ Sp W) {P M : LB G} {N : LB (pullback p (spMap (algebraMap W K')))}
    (w : LB.Iso (M.pull (pullback.fst p (spMap (algebraMap W K')))) N)
    (w₁ : LB.Iso (P.pull (pullback.fst p (spMap (algebraMap W K')))) N) : Prop :=
  ∃ (e₀ : Sp W ⟶ G) (_ : e₀ ≫ p = 𝟙 _) (x : Sp K' ⟶ pullback p (spMap (algebraMap W K')))
    (_ : x ≫ pullback.fst p (spMap (algebraMap W K')) = spMap (algebraMap W K') ≫ e₀)
    (_ : x ≫ pullback.snd p (spMap (algebraMap W K')) = 𝟙 _)
    (i : P.ι) (m : M.ι) (n : N.ι) (_ : ⊤ ≤ e₀ ⁻¹ᵁ P.U i) (_ : ⊤ ≤ e₀ ⁻¹ᵁ M.U m)
    (h₁ : ⊤ ≤ x ⁻¹ᵁ (N.U n ⊓ (P.pull (pullback.fst p (spMap (algebraMap W K')))).U (fun _ => i)))
    (h₂ : ⊤ ≤ x ⁻¹ᵁ (N.U n ⊓ (M.pull (pullback.fst p (spMap (algebraMap W K')))).U (fun _ => m)))
    (a : W),
    (Scheme.ΓSpecIso (CommRingCat.of K')).hom.hom ((x.appLE _ ⊤ h₁).hom (w₁.s (n, fun _ => i)).val) =
      algebraMap W K' a * (Scheme.ΓSpecIso (CommRingCat.of K')).hom.hom
        ((x.appLE _ ⊤ h₂).hom (w.s (n, fun _ => m)).val)

end GlobalTheory.SectionLattice
