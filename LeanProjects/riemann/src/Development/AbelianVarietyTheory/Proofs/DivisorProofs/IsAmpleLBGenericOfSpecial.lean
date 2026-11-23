import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.KawamataViehweg
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsAlgClosedBaseChange
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAffineOpenPreimageOfIsPullback
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.RelAmpleOfAmpleOnClosedSubschemeLocalBase
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverMorphismRestrictOfRelAmple
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverIffIsProperAndExistsIsAmpleLB
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverCompOfIsClosedImmersion
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsProperOfIsProjBy
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.PolBaseChangeOfRelAmpleLocal
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.CechPic GlobalTheory.QCoh

namespace GlobalTheory.AmpleGeneric

theorem isAmpleLB_generic_of_special : ∀ (O E κ : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field E] [Algebra O E] [Field κ] [Algebra O κ], Function.Surjective (algebraMap O κ) → ∀ (W C W₀ : Scheme.{0}) (f : W ⟶ Sp O) (q : C ⟶ Sp E) (φ : C ⟶ W) (f₀ : W₀ ⟶ Sp κ) (b : W₀ ⟶ W), IsProjOver f → Flat f → IsPullback φ q f (spMap (algebraMap O E)) → IsPullback b f₀ f (spMap (algebraMap O κ)) → ∀ M : LB W, M.IsLB → IsAmpleLB (M.pull b) → IsAmpleLB (M.pull φ) := by
  intro O E κ _ _ _ _ _ _ _ hs W C W₀ f q φ f₀ b hP hF H H₀ M hM hA₀
  have hP₀ : IsProjOver f₀ := GlobalTheory.ProjSpace.isProjOver_of_isPullback_spMap _ H₀ hP
  have hB₀ : GlobalTheory.AbLaw.IsProjBy f₀ := (GlobalTheory.ProjSpace.isProjBy_iff_isProjOver f₀).2 hP₀
  have hB : GlobalTheory.AbLaw.IsProjBy f := (GlobalTheory.ProjSpace.isProjBy_iff_isProjOver f).2 hP
  have : IsProper (Over.mk f₀).hom := GlobalTheory.AbLaw.isProper_of_isProjBy κ W₀ f₀ hB₀
  have hR₀ : ReciprocityTheory.ChartRestriction.G.Out.RelAmple (Over.mk f₀) (M.pull b) :=
    (GlobalTheory.relAmple_iff_isAmpleLB_of_isAffine (Over.mk f₀) (LB.isLB_pull hM b)).2 hA₀
  have hR : ReciprocityTheory.ChartRestriction.G.Out.RelAmple (Over.mk f) M :=
    GlobalTheory.AmpleLocalBase.relAmple_of_closed O (Over.mk f) M hF hB hM κ (algebraMap O κ) hs (Over.mk f₀) b H₀
      (M.pull b) (LB.isLB_pull hM b) (GlobalTheory.lbIso_refl (LB.isLB_pull hM b)) hR₀
  have hAmp : IsAmpleLB M := GlobalTheory.isAmpleLB_of_relAmple_of_isAffine (Over.mk f) hM hR
  have : IsAffineHom φ := MorphismProperty.of_isPullback H.flip inferInstance
  exact hAmp.pull_of_isAffineHom φ

end GlobalTheory.AmpleGeneric
