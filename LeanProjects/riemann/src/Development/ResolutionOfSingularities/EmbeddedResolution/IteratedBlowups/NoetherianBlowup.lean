import Mathlib
import Development.ResolutionOfSingularities.Foundations.Blowup.BlowupProper
import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.BlowupSequenceBasic
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.AffineSpaceCoordinates
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.AffineResolutionRule
import Development.ResolutionOfSingularities.Foundations.Schemes.AffineOpens
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.FunctorialPrincipalization
import Development.ResolutionOfSingularities.EmbeddedResolution.StrongResolution.EmbeddedStrictTransform
import Development.ResolutionOfSingularities.EmbeddedResolution.StrongResolution.DiscardedLocus
import Development.ResolutionOfSingularities.Foundations.BlowupUniversalProperty
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionOfSingularities
universe u

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits

namespace FunctorialResolution.EmbeddedResolution

theorem isNoetherian_of_locallyOfFiniteType {X Y : Scheme.{u}} (f : X ⟶ Y)
    [AlgebraicGeometry.IsNoetherian Y] [AlgebraicGeometry.LocallyOfFiniteType f]
    [AlgebraicGeometry.QuasiCompact f] :
    AlgebraicGeometry.IsNoetherian X := by
  have : AlgebraicGeometry.IsLocallyNoetherian X :=
    AlgebraicGeometry.LocallyOfFiniteType.isLocallyNoetherian f
  have : CompactSpace ↥X := AlgebraicGeometry.QuasiCompact.compactSpace_of_compactSpace f
  constructor

theorem isNoetherian_of_iso {X Y : Scheme.{u}} (e : X ≅ Y)
    [AlgebraicGeometry.IsNoetherian X] :
    AlgebraicGeometry.IsNoetherian Y := by
  have : AlgebraicGeometry.LocallyOfFiniteType e.inv := inferInstance
  have : AlgebraicGeometry.QuasiCompact e.inv := inferInstance
  exact isNoetherian_of_locallyOfFiniteType e.inv

theorem isNoetherian_of_isBlowupAlongIdealSheaf {X X' : Scheme.{u}} [AlgebraicGeometry.IsNoetherian X]
    {π : X' ⟶ X} {I : X.IdealSheafData} (h : Blowup.IsBlowupAlongIdealSheaf π I) :
    AlgebraicGeometry.IsNoetherian X' := by
  have : AlgebraicGeometry.IsProper π := Blowup.blowupIsProper.{u} X X' π I h
  have : AlgebraicGeometry.LocallyOfFiniteType π := inferInstance
  have : AlgebraicGeometry.QuasiCompact π := inferInstance
  exact isNoetherian_of_locallyOfFiniteType π

instance instIsNoetherianAffineSpaceIdx (k : Type u) [Field k] (n : Type u) [Finite n] :
    AlgebraicGeometry.IsNoetherian (affineSpaceIndexedBy k n) := by
  have : IsNoetherianRing ↑(CommRingCat.of (MvPolynomial n k)) :=
    inferInstanceAs (IsNoetherianRing (MvPolynomial n k))
  have : AlgebraicGeometry.IsNoetherian
      (Spec (CommRingCat.of (MvPolynomial n k))) := inferInstance
  exact isNoetherian_of_iso
    (AlgebraicGeometry.AffineSpace.SpecIso n (CommRingCat.of k)).symm

theorem isNoetherian_schemeAt {X : Scheme.{u}} (B : SequenceOfBlowups X)
    [AlgebraicGeometry.IsNoetherian X] (i : ℕ) (hi : i ≤ B.length) :
    AlgebraicGeometry.IsNoetherian (B.schemeAt i) := by
  revert hi
  induction i with
  | zero =>
    intro _
    exact isNoetherian_of_iso B.isoZero.symm
  | succ n ih =>
    intro hi
    have hn : n < B.length := hi
    exact @isNoetherian_of_isBlowupAlongIdealSheaf (B.schemeAt n) (B.schemeAt (n + 1)) (ih (le_of_lt hn)) _ _
      (B.isBlowupAlongIdealSheaf_blowupMorphism n hn)

instance SequenceOfBlowups.instIsNoetherianTop {X : Scheme.{u}} (B : SequenceOfBlowups X)
    [AlgebraicGeometry.IsNoetherian X] : AlgebraicGeometry.IsNoetherian B.lastObj :=
  isNoetherian_schemeAt B B.length le_rfl

theorem isNoetherian_ambientLevel {k : Type u} [Field k] [CharZero k] {Y : Scheme.{u}}
    [AlgebraicGeometry.IsAffine Y] {pY : Y ⟶ Spec (CommRingCat.of k)}
    [AlgebraicGeometry.LocallyOfFiniteType pY] (S : AffineSpacePrincipalizationData k Y pY) (i : ℕ)
    (hi : i ≤ S.ambientLength) :
    AlgebraicGeometry.IsNoetherian (S.ambientLevel i) := by
  revert hi
  induction i with
  | zero =>
    intro _
    have : AlgebraicGeometry.IsNoetherian S.ambient :=
      instIsNoetherianAffineSpaceIdx k (ULift.{u, 0} (Fin S.dim))
    exact isNoetherian_of_iso S.ambientBlowups.isoZero.symm
  | succ n ih =>
    intro hi
    have hn : n < S.ambientLength := hi
    exact @isNoetherian_of_isBlowupAlongIdealSheaf (S.ambientLevel n) (S.ambientLevel (n + 1)) (ih (le_of_lt hn)) _ _
      (S.ambientBlowups.isBlowupAlongIdealSheaf_blowupMorphism n hn)

theorem embeddedPrincipalizationAmbientIsNoetherian (A : PrincipalizationAlgorithm.{u}) (hemb : AffineEmbedsIntoAffineSpace.{u})
    (hsnc : NilIsStrictNormalCrossingsOnAffineSpace.{u}) (hsm : AffineSpaceIsSmooth.{u}) :
    EmbeddedPrincipalizationAmbientIsNoetherian A hemb hsnc hsm := by
  intro k _ _ Y pY _ _ _ _ i hi
  exact isNoetherian_ambientLevel (AffineSpacePrincipalizationData.ofAffine A hemb hsnc hsm k Y pY) i hi

end FunctorialResolution.EmbeddedResolution
