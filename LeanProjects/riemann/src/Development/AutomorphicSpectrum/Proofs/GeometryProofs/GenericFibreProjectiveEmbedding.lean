import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsSncPatchRat
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.EmbedsGeneric
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverCompOfIsClosedImmersion
import Development.AbelianVarietyTheory.Counterexamples.ModuliSurvey.IsQProjOverOfIsProjOver
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsIsoStalkMapOfFlatOfSurjectiveOnStalks
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.SncBase

namespace GlobalTheory.CompanionTheory.Ar.SncBase

theorem genericFibre_reduced_noetherian_closed : ∀ (F : Type) [Field F] [NumberField F] (P : Scheme.{0}) (s : P ⟶ Sp (𝓞 F)), IsProjOver s → Tor.IsNormalScheme P → IsReduced (pullback s (spMap (algebraMap (𝓞 F) F))) ∧ IsLocallyNoetherian (pullback s (spMap (algebraMap (𝓞 F) F))) ∧ ∃ (M : ℕ) (i : pullback s (spMap (algebraMap (𝓞 F) F)) ⟶ PSpace F M), IsClosedImmersion i ∧ i ≫ PSpace.str F M = pullback.snd _ _ := by
  intro F _ _ P s hs hn
  have hp : IsProjOver (pullback.snd s (spMap (algebraMap (𝓞 F) F))) :=
    GlobalTheory.ProjSpace.isProjOver_pullback_snd _ hs
  have hb : IsPreimmersion (spMap (algebraMap (𝓞 F) F)) :=
    IsPreimmersion.of_isLocalization (R := CommRingCat.of (𝓞 F)) (S := F) (nonZeroDivisors (𝓞 F))
  have hbf : Flat (spMap (algebraMap (𝓞 F) F)) := by
    rw [Flat.SpecMap_iff]
    exact RingHom.flat_algebraMap_iff.mpr (IsLocalization.flat F (nonZeroDivisors (𝓞 F)))
  have h1 : IsPreimmersion (pullback.fst s (spMap (algebraMap (𝓞 F) F))) :=
    MorphismProperty.of_isPullback (P := @IsPreimmersion) (IsPullback.of_hasPullback _ _).flip hb
  have hiso := GlobalTheory.isIso_stalkMap_of_flat_of_surjectiveOnStalks (pullback.fst s (spMap (algebraMap (𝓞 F) F)))
  have := GlobalTheory.SchemeWords.isProper_of_isProjOver hp
  refine ⟨?_, LocallyOfFiniteType.isLocallyNoetherian (pullback.snd s (spMap (algebraMap (𝓞 F) F))), hp⟩
  have : ∀ x, _root_.IsReduced ((pullback s (spMap (algebraMap (𝓞 F) F))).presheaf.stalk x) := fun x => by
    have := hiso x
    have i := (asIso ((pullback.fst s (spMap (algebraMap (𝓞 F) F))).stalkMap x)).commRingCatIsoToRingEquiv
    obtain ⟨_, _⟩ := hn (pullback.fst s (spMap (algebraMap (𝓞 F) F)) x)
    exact isReduced_of_injective i.symm i.symm.injective
  exact isReduced_of_isReduced_stalk _

end GlobalTheory.CompanionTheory.Ar.SncBase
