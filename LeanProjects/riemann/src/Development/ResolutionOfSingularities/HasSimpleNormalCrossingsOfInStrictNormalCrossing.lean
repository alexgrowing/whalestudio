import Development.ResolutionOfSingularities.Statements
import Development.ResolutionOfSingularities.EmbeddedResolution.HironakaTheorem
import Development.ResolutionOfSingularities.EmbeddedResolution.StrictTransformCharts.StrictNormalCrossingsBlowup
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.FunctorialPrincipalization
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.IdealBlowupSequenceBoundary
import Development.ResolutionOfSingularities.Foundations.Schemes.IdealSheafData
import Development.ResolutionOfSingularities.EmbeddedResolution.StrongResolution.PrincipalizationWithRadicalCenters

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace FunctorialResolution

theorem functorialResolutionCharZero : FunctorialResolutionCharZero.{u} := by
  obtain ⟨R, h1, h2, h3⟩ := EmbeddedResolution.strongResolutionOfSingularitiesCharZero.{u}
  exact ⟨fun k _ _ X f _ _ _ =>
    ⟨(R k X f).length, (R k X f).tower, (R k X f).isoZero, (R k X f).center, (R k X f).isBlowup⟩, h1, h2, h3⟩

theorem inStrictNormalCrossingPosition_of_hasSimpleNormalCrossings {X : Scheme.{u}} {k : Type u} [Field k]
    {p : X ⟶ Spec (CommRingCat.of k)} {E : List X.IdealSheafData} (h : HasSimpleNormalCrossings p E) :
    FunctorialResolution.EmbeddedResolution.InStrictNormalCrossingPosition p E := by
  refine ⟨h.1, fun x => ?_⟩
  obtain ⟨U, hx, m, c, hc, he, a, h1, h2, h3⟩ := h.2 x
  exact ⟨U, hx, m, ⟨c, hc, he⟩, a, h1, h2, h3⟩

theorem hasSimpleNormalCrossingsWith_of_hasStrictNormalCrossingsWith {X : Scheme.{u}} {k : Type u} [Field k]
    {p : X ⟶ Spec (CommRingCat.of k)} {Z : X.IdealSheafData} {E : List X.IdealSheafData}
    (h : FunctorialResolution.EmbeddedResolution.HasStrictNormalCrossingsWith p Z E) : HasSimpleNormalCrossingsWith p Z E := by
  intro x hx
  obtain ⟨U, hxU, m, c, a, S, h1, h2, h3, h4⟩ := h x hx
  exact ⟨U, hxU, m, c.map, c.comp_struct, c.isEtale, a, S, h1, h2, h3, h4⟩

noncomputable def blowupSequenceOfIdealBlowupSequence {k : Type u} [Field k] {X : Scheme.{u}}
    {p : X ⟶ Spec (CommRingCat.of k)} {I : X.IdealSheafData} {E : List X.IdealSheafData}
    (M : FunctorialResolution.EmbeddedResolution.IdealBlowupSequence p I E) : BlowupSequence X :=
  ⟨M.length, M.tower, M.isoZero, M.center, M.isBlowup⟩

theorem hasSimpleNormalCrossings_of_inStrictNormalCrossingPosition {X : Scheme.{u}} {k : Type u} [Field k]
    {p : X ⟶ Spec (CommRingCat.of k)} {E : List X.IdealSheafData} (h : FunctorialResolution.EmbeddedResolution.InStrictNormalCrossingPosition p E) :
    HasSimpleNormalCrossings p E := by
  refine ⟨h.1, fun x => ?_⟩
  obtain ⟨U, hx, m, c, a, h1, h2, h3⟩ := h.2 x
  exact ⟨U, hx, m, c.map, c.comp_struct, c.isEtale, a, h1, h2, h3⟩

theorem isPrincipalizingSequence_of_idealBlowupSequence {k : Type u} [Field k] {X : Scheme.{u}}
    {p : X ⟶ Spec (CommRingCat.of k)} [Smooth p] [LocallyOfFiniteType p] [QuasiCompact p]
    {I : X.IdealSheafData} {E : List X.IdealSheafData}
    (M : FunctorialResolution.EmbeddedResolution.IdealBlowupSequence p I E) (hE : FunctorialResolution.EmbeddedResolution.InStrictNormalCrossingPosition p E) (hM : M.lastIdeal = ⊤) :
    IsPrincipalizingSequence p I E (blowupSequenceOfIdealBlowupSequence M) := by
  have : AlgebraicGeometry.IsNoetherian X := FunctorialResolution.EmbeddedResolution.isNoetherian_of_locallyOfFiniteType p
  have key : ∀ i, i ≤ M.length →
      I.comap ((blowupSequenceOfIdealBlowupSequence M).structMap i) =
        (blowupSequenceOfIdealBlowupSequence M).exceptionalProduct i *
          (show ((blowupSequenceOfIdealBlowupSequence M).obj i).IdealSheafData from M.ideal i) := by
    intro i
    induction i with
    | zero =>
      intro _
      change _ = ⊤ * _
      rw [← Scheme.IdealSheafData.one_eq_top, one_mul]
      exact M.ideal_zero.symm
    | succ n ih =>
      intro hn
      have hlt : n < M.length := hn
      have hcomp : (blowupSequenceOfIdealBlowupSequence M).structMap (n + 1) =
          (blowupSequenceOfIdealBlowupSequence M).blowupMap n ≫ (blowupSequenceOfIdealBlowupSequence M).structMap n :=
        ((blowupSequenceOfIdealBlowupSequence M).structMap_down (Nat.le_succ n)).symm
      have hsucc : (M.center n).comap ((blowupSequenceOfIdealBlowupSequence M).blowupMap n) *
          (show ((blowupSequenceOfIdealBlowupSequence M).obj (n + 1)).IdealSheafData from M.ideal (n + 1)) =
          (show ((blowupSequenceOfIdealBlowupSequence M).obj n).IdealSheafData from M.ideal n).comap
            ((blowupSequenceOfIdealBlowupSequence M).blowupMap n) := M.ideal_succ n hlt
      rw [hcomp, Scheme.IdealSheafData.comap_comp, ih hlt.le, Scheme.IdealSheafData.comap_mul, ← hsucc,
        ← mul_assoc]
      rfl
  refine ⟨M.ideal, M.boundary, M.ideal_zero, M.boundary_zero, M.center_smooth,
    fun i hi => hasSimpleNormalCrossingsWith_of_hasStrictNormalCrossingsWith (M.center_snc i hi), M.ideal_vanishes,
    M.ideal_succ, M.boundary_succ, hM, ?_, fun i hi => M.smooth_structureMorphism i hi,
    fun i hi => hasSimpleNormalCrossings_of_inStrictNormalCrossingPosition (M.inStrictNormalCrossingPosition_boundary_of_isNoetherian hE i hi)⟩
  have hfin : (show ((blowupSequenceOfIdealBlowupSequence M).obj M.length).IdealSheafData from M.ideal M.length) = ⊤ := hM
  refine (key M.length le_rfl).trans ?_
  rw [hfin, ← Scheme.IdealSheafData.one_eq_top, mul_one]
  rfl

noncomputable def principalizationRuleOfAlgorithm (A : EmbeddedResolution.PrincipalizationAlgorithm.{u}) : PrincipalizationRuleCharZero.{u} :=
  fun k _ _ X p _ _ _ I hI E hE =>
    blowupSequenceOfIdealBlowupSequence (A k X p I hI E (inStrictNormalCrossingPosition_of_hasSimpleNormalCrossings hE))

theorem functorialPrincipalizationCharZero_of_algorithm (A : EmbeddedResolution.PrincipalizationAlgorithm.{u}) (h : FunctorialResolution.EmbeddedResolution.IsFunctorialPrincipalization A) :
    FunctorialPrincipalizationCharZero.{u} := by
  refine ⟨principalizationRuleOfAlgorithm A, ?_, ?_, ?_⟩
  · intro k _ _ X p _ _ _ I hI E hE
    exact isPrincipalizingSequence_of_idealBlowupSequence _ (inStrictNormalCrossingPosition_of_hasSimpleNormalCrossings hE)
      (h.lastIdeal_eq_top k X p I hI E (inStrictNormalCrossingPosition_of_hasSimpleNormalCrossings hE))
  · intro k _ _ X p _ _ _ I hI E hE X' p' _ _ _ φ _ hφ hI' hE'
    exact h.smooth_pullback k X p I hI E (inStrictNormalCrossingPosition_of_hasSimpleNormalCrossings hE) X' p' φ hφ hI'
      (inStrictNormalCrossingPosition_of_hasSimpleNormalCrossings hE')
  · intro k _ _ X p _ _ _ I hI E hE K _ _ _ hI' hE'
    exact h.base_change k X p I hI E (inStrictNormalCrossingPosition_of_hasSimpleNormalCrossings hE) K (algebraMap k K) hI'
      (inStrictNormalCrossingPosition_of_hasSimpleNormalCrossings hE')

theorem functorialPrincipalizationCharZero : FunctorialPrincipalizationCharZero.{u} :=
  functorialPrincipalizationCharZero_of_algorithm FunctorialResolution.EmbeddedResolution.principalizationWithRadicalCenters FunctorialResolution.EmbeddedResolution.isFunctorialPrincipalization_principalizationWithRadicalCenters

end FunctorialResolution
