import Mathlib
import Development.ResolutionOfSingularities.Foundations.Blowup.BlowupProperties
import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.ClopenRestriction
import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.BlowupSequenceRelations
import Development.ResolutionOfSingularities.Foundations.Blowup.StrictTransform
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.StrictNormalCrossings
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.StrictNormalCrossingsSmoothBaseChange
import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.IdealSheafOrder
import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.OrderAtMultiplicativity
import Development.ResolutionOfSingularities.EmbeddedResolution.MaximalContactHypersurfaces.TunedSheaf
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReductionProperties
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.ContainedComponentsIdeal
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.PushedBlowupSequence
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.DivisorReductionSequence
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.LowerBoundaryAfterBlowup
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.AmbientBlowupSequence
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.LowerBoundaryData
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.AmbientCenterImage
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.KernelOfAmbientEmbedding
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedOrderReduction.OrderAlongBlowupSequence
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.MaxContactReduction
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.AmbientEmbedding
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.BlowupSequenceData
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.IrreducibleComponentsAlongSequence
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.ControlledTransform
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.IdealBlowupSequence
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.MarkedSequenceOfBlowups
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.SingleBlowup
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.MarkedSequenceTransforms
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.IteratedComapDivisor
import Development.ResolutionOfSingularities.Foundations.BlowupUniversalProperty
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionOfSingularities
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.CoordinateDivisorSmoothness
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.ChartRing
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.CoordinateSubscheme
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.EtaleCoordinates
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.EtaleChartExistence
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.PolynomialCoordinateExtension
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.SmoothCenterChart
import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.DerivativeIdealSheaf
import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.DerivativeIdealEtaleBaseChange
import Development.ResolutionOfSingularities.Foundations.Schemes.IdealSheafData
import Development.ResolutionOfSingularities.Foundations.Blowup.BlowupBasic
import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.NoetherianBlowup
import Development.ResolutionOfSingularities.EmbeddedResolution.StrictTransformCharts.ControlledTransform
import Development.ResolutionOfSingularities.EmbeddedResolution.StrictTransformCharts.CoordinateBlowupChart
import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.Saturation
import Development.ResolutionOfSingularities.EmbeddedResolution.StrictTransformCharts.BlowupChart
import Development.ResolutionOfSingularities.Foundations.Blowup.BlowupCoproduct
import Development.ResolutionOfSingularities.Foundations.Blowup.BlowupExistence
import Development.ResolutionOfSingularities.Foundations.Blowup.BlowupOpenCover
import Development.ResolutionOfSingularities.Foundations.Blowup.BlowupProper
import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.StrictTransform
import Development.ResolutionOfSingularities.EmbeddedResolution.StrictTransformCharts.CoordinateDivisorBlowup
import Development.ResolutionOfSingularities.EmbeddedResolution.StrictTransformCharts.StrictTransformChart
import Development.ResolutionOfSingularities.EmbeddedResolution.StrictTransformCharts.StrictNormalCrossingsBlowup
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.IdealSheafOpenRestriction
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.StrictNormalCrossingsWithoutUnitIdeals
import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.PowerContainmentAndOrderLocus
import Development.ResolutionOfSingularities.Foundations.Schemes.SchemeMorphismProperties
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.SupportsAlongSequence
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.ComapSubschemeIso
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.PrincipalizationCertificate
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DimensionRecursion
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedOrderReduction.OrderReductionAlgorithm
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.PrincipalizationConstruction
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.FunctorialPrincipalization
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.IsoInvariance
import Development.ResolutionOfSingularities.EmbeddedResolution.StrongResolution.EmbeddedStrictTransform
import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.OrderAtGenericPoint
universe u

open CategoryTheory AlgebraicGeometry

noncomputable section

namespace FunctorialResolution.EmbeddedResolution

private theorem not_natCast_add_one_le_self (n : ℕ) : ¬ ((n : ℕ∞) + 1 ≤ (n : ℕ∞)) := by
  rw [ENat.add_one_le_iff (ENat.natCast_ne_top n)]
  exact lt_irrefl _

private def iteratedStrictTransform {X : Scheme.{u}} (d : BlowupSequenceData X)
    (A0 : (d.obj 0).IdealSheafData) (t : ℕ) : (d.obj t).IdealSheafData :=
  Nat.rec (motive := fun n => (d.obj n).IdealSheafData) A0
    (fun n ih => Blowup.strictTransform (d.map n) (d.center n) ih) t

private theorem strictTransformIter_succ {X : Scheme.{u}} (d : BlowupSequenceData X)
    (A0 : (d.obj 0).IdealSheafData) (t : ℕ) :
    iteratedStrictTransform d A0 (t + 1) =
      Blowup.strictTransform (d.map t) (d.center t) (iteratedStrictTransform d A0 t) := rfl

private theorem length_le_length_boundary {k : Type u} [Field k] {X : Scheme.{u}}
    {p : X ⟶ Spec (CommRingCat.of k)} {I : X.IdealSheafData} {m : ℕ}
    {E : List X.IdealSheafData} (S : MarkedSequenceOfBlowups p I m E) (n : ℕ) :
    n ≤ S.length → E.length ≤ (S.boundary n).length := by
  induction n with
  | zero =>
    intro _
    simp [S.boundary_zero]
  | succ n ih =>
    intro hn
    have h1 := ih (by omega)
    have h2 : (S.boundary (n + 1)).length = (S.boundary n).length + 1 := by
      rw [S.boundary_succ n (by omega)]
      simp
    omega

private theorem boundary_zero_get_eq_comap {k : Type u} [Field k] {X : Scheme.{u}}
    {p : X ⟶ Spec (CommRingCat.of k)} {I : X.IdealSheafData} {m : ℕ}
    {E : List X.IdealSheafData} (S : MarkedSequenceOfBlowups p I m E) (j : ℕ) (hj : j < E.length)
    (h : j < (S.boundary 0).length) :
    (S.boundary 0).get ⟨j, h⟩ = (E.get ⟨j, hj⟩).comap S.isoZero.hom := by
  have hb := S.boundary_zero
  rw [List.get_eq_getElem, List.get_eq_getElem, List.getElem_of_eq hb h, List.getElem_map]

private theorem boundary_succ_get_eq_strictTransform {k : Type u} [Field k] {X : Scheme.{u}}
    {p : X ⟶ Spec (CommRingCat.of k)} {I : X.IdealSheafData} {m : ℕ}
    {E : List X.IdealSheafData} (S : MarkedSequenceOfBlowups p I m E) (j n : ℕ) (hn : n < S.length)
    (hjn : j < (S.boundary n).length) (h : j < (S.boundary (n + 1)).length) :
    (S.boundary (n + 1)).get ⟨j, h⟩ =
      Blowup.strictTransform (S.transitionMapSucc n) (S.center n) ((S.boundary n).get ⟨j, hjn⟩) := by
  have hb := S.boundary_succ n hn
  have hlen : j < (List.map (Blowup.strictTransform (S.transitionMapSucc n) (S.center n))
      (S.boundary n)).length := by
    rw [List.length_map]
    exact hjn
  rw [List.get_eq_getElem, List.get_eq_getElem, List.getElem_of_eq hb h]
  simp [List.getElem_append_left hlen]

private theorem containedComponentsIdeal_pow_mul_lowerIdealAfterBlowup (T : MarkedIdealWithBoundary.{u}) (hV : T.IsAdmissible) (j : ℕ)
    (hj : j < T.boundary.length) :
    DivisorReduction.containedComponentsIdeal T j hj ^ T.mult * DivisorReduction.lowerIdealAfterBlowup T j hj = T.ideal := by
  obtain ⟨J, hJ⟩ := exists_mul_pow_containedComponentsIdeal_eq_ideal T hV j hj
  have hex : Blowup.exceptionalIdeal (𝟙 T.scheme) (DivisorReduction.containedComponentsIdeal T j hj)
      = DivisorReduction.containedComponentsIdeal T j hj := by
    rw [Blowup.exceptionalIdeal_eq_comap, Scheme.IdealSheafData.comap_id]
  have hA : (T.ideal.comap (𝟙 T.scheme)).comap (𝟙 T.scheme) = T.ideal := by
    rw [Scheme.IdealSheafData.comap_id, Scheme.IdealSheafData.comap_id]
  have h1 : ∃ B, Blowup.exceptionalIdeal (𝟙 T.scheme) (DivisorReduction.containedComponentsIdeal T j hj) ^ T.mult * B
      = (T.ideal.comap (𝟙 T.scheme)).comap (𝟙 T.scheme) := by
    refine ⟨J, ?_⟩
    rw [hex, hA]
    exact hJ
  have h2 := pow_mul_residualByPow ((T.ideal.comap (𝟙 T.scheme)).comap (𝟙 T.scheme))
    (Blowup.exceptionalIdeal (𝟙 T.scheme) (DivisorReduction.containedComponentsIdeal T j hj)) T.mult h1
  rw [hex, hA] at h2
  unfold DivisorReduction.lowerIdealAfterBlowup
  rw [hex, hA]
  exact h2

namespace TransportedDivisor

theorem support_iteratedComap {X : Scheme.{u}} (d : BlowupSequenceData X) (B : (d.obj 0).IdealSheafData)
    (t : ℕ) :
    (↑(iteratedComap d B t).support : Set ↥(d.obj t)) =
      ⇑(d.projectionToBase t ≫ d.isoZero.inv) ⁻¹' (↑B.support : Set ↥(d.obj 0)) := by
  induction t with
  | zero =>
    have h0 : d.projectionToBase 0 ≫ d.isoZero.inv = 𝟙 (d.obj 0) := by
      rw [BlowupSequenceData.projectionToBase_zero]
      exact d.isoZero.hom_inv_id
    rw [iteratedComap_zero, h0]
    ext x
    simp only [Set.mem_preimage, Scheme.Hom.id_base, TopCat.id_app]
  | succ t ih =>
    have hcomp : d.projectionToBase (t + 1) ≫ d.isoZero.inv
        = d.map t ≫ (d.projectionToBase t ≫ d.isoZero.inv) := by
      rw [BlowupSequenceData.projectionToBase_succ, Category.assoc]
    ext x
    rw [iteratedComap_succ]
    have hmem : x ∈ (↑((iteratedComap d B t).comap (d.map t)).support :
          Set ↥(d.obj (t + 1))) ↔
        d.map t x ∈ (↑(iteratedComap d B t).support : Set ↥(d.obj t)) :=
      Scheme.IdealSheafData.mem_support_comap
    rw [hmem, ih, hcomp]
    simp only [Set.mem_preimage, Scheme.Hom.comp_apply]

end TransportedDivisor

namespace DivisorReduction

theorem disjoint_support_lowerIdealAfterBlowup_containedComponentsIdeal (T : MarkedIdealWithBoundary.{u}) (hV : T.IsAdmissible)
    (hord : ∀ x : ↥T.scheme, orderAt T.ideal x ≤ (T.mult : ℕ∞))
    (j : ℕ) (hj : j < T.boundary.length) :
    Disjoint ((lowerIdealAfterBlowup T j hj).support : Set ↥T.scheme)
      ((containedComponentsIdeal T j hj).support : Set ↥T.scheme) := by
  have := hV.charZero
  have := hV.smooth
  rw [Set.disjoint_left]
  intro x hx1 hx2
  have hkey := containedComponentsIdeal_pow_mul_lowerIdealAfterBlowup T hV j hj
  have ha : 1 ≤ orderAt (containedComponentsIdeal T j hj) x :=
    (one_le_orderAt_iff_mem_support _ _).2 hx2
  have hbb : 1 ≤ orderAt (lowerIdealAfterBlowup T j hj) x :=
    (one_le_orderAt_iff_mem_support _ _).2 hx1
  have h3 : orderAt T.ideal x
      = (T.mult : ℕ∞) * orderAt (containedComponentsIdeal T j hj) x
        + orderAt (lowerIdealAfterBlowup T j hj) x := by
    rw [← hkey, orderAt_mul T.base T.structMap, orderAt_pow T.base T.structMap]
  have hm : (T.mult : ℕ∞) ≤ (T.mult : ℕ∞) * orderAt (containedComponentsIdeal T j hj) x := by
    calc (T.mult : ℕ∞) = (T.mult : ℕ∞) * 1 := (mul_one _).symm
      _ ≤ (T.mult : ℕ∞) * orderAt (containedComponentsIdeal T j hj) x := by gcongr
  have hordGe : (T.mult : ℕ∞) + 1 ≤ orderAt T.ideal x := by
    rw [h3]
    exact add_le_add hm hbb
  exact not_natCast_add_one_le_self T.mult (le_trans hordGe (hord x))

private theorem ambientBlowupSeq_isoObjZero_hom (hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u})
    (hno : BlowupPreservesNoetherian.{u}) (T : MarkedIdealWithBoundary.{u})
    [AlgebraicGeometry.IsNoetherian T.scheme] (j : ℕ) (hj : j < T.boundary.length)
    (I₀ : T.scheme.IdealSheafData) (E₀ : List T.scheme.IdealSheafData)
    (s : (restrictToBoundaryDivisor T j hj I₀ E₀).SequenceOfBlowups)
    (hpr : (MarkedBlowupSequenceData.ofMarkedSequence s).toBlowupSequenceData.CentersContainNoComponent) :
    (ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).isoZero.hom = 𝟙 T.scheme :=
  congrArg Iso.hom (ambientBlowupSequence_isoObjZero (T.boundary.get ⟨j, hj⟩).subschemeι
    (MarkedBlowupSequenceData.ofMarkedSequence s).toBlowupSequenceData hres hno hpr)

private theorem ambientBlowupSeq_isoObjZero_inv (hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u})
    (hno : BlowupPreservesNoetherian.{u}) (T : MarkedIdealWithBoundary.{u})
    [AlgebraicGeometry.IsNoetherian T.scheme] (j : ℕ) (hj : j < T.boundary.length)
    (I₀ : T.scheme.IdealSheafData) (E₀ : List T.scheme.IdealSheafData)
    (s : (restrictToBoundaryDivisor T j hj I₀ E₀).SequenceOfBlowups)
    (hpr : (MarkedBlowupSequenceData.ofMarkedSequence s).toBlowupSequenceData.CentersContainNoComponent) :
    (ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).isoZero.inv = 𝟙 T.scheme :=
  congrArg Iso.inv (ambientBlowupSequence_isoObjZero (T.boundary.get ⟨j, hj⟩).subschemeι
    (MarkedBlowupSequenceData.ofMarkedSequence s).toBlowupSequenceData hres hno hpr)

private theorem ambientBlowupSeq_projectionToBase_zero_comp_structureMorphism (hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u})
    (hno : BlowupPreservesNoetherian.{u}) (T : MarkedIdealWithBoundary.{u})
    [AlgebraicGeometry.IsNoetherian T.scheme] (j : ℕ) (hj : j < T.boundary.length)
    (I₀ : T.scheme.IdealSheafData) (E₀ : List T.scheme.IdealSheafData)
    (s : (restrictToBoundaryDivisor T j hj I₀ E₀).SequenceOfBlowups)
    (hpr : (MarkedBlowupSequenceData.ofMarkedSequence s).toBlowupSequenceData.CentersContainNoComponent) :
    (ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).projectionToBase 0 ≫ T.structMap = T.structMap := by
  have h1 : (ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).projectionToBase 0 = 𝟙 T.scheme :=
    (BlowupSequenceData.projectionToBase_zero _).trans (ambientBlowupSeq_isoObjZero_hom hres hno T j hj I₀ E₀ s hpr)
  rw [h1]
  exact Category.id_comp T.structMap

private theorem ambientBlowupSeq_projectionToBase_comp_isoObjZero_inv (hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u})
    (hno : BlowupPreservesNoetherian.{u}) (T : MarkedIdealWithBoundary.{u})
    [AlgebraicGeometry.IsNoetherian T.scheme] (j : ℕ) (hj : j < T.boundary.length)
    (I₀ : T.scheme.IdealSheafData) (E₀ : List T.scheme.IdealSheafData)
    (s : (restrictToBoundaryDivisor T j hj I₀ E₀).SequenceOfBlowups)
    (hpr : (MarkedBlowupSequenceData.ofMarkedSequence s).toBlowupSequenceData.CentersContainNoComponent) (n : ℕ) :
    (ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).projectionToBase n ≫
        (ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).isoZero.inv
      = (ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).projectionToBase n := by
  rw [ambientBlowupSeq_isoObjZero_inv hres hno T j hj I₀ E₀ s hpr]
  exact Category.comp_id ((ambientBlowupSeq hres hno T j hj I₀ E₀ s hpr).projectionToBase n)

private theorem prependedAmbientSeq_length (hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u})
    (hno : BlowupPreservesNoetherian.{u}) (T : MarkedIdealWithBoundary.{u})
    [AlgebraicGeometry.IsNoetherian T.scheme] (j : ℕ) (hj : j < T.boundary.length)
    (hb : Blowup.IsBlowupAlongIdealSheaf (𝟙 T.scheme) (containedComponentsIdeal T j hj))
    (s : (restrictTwistedToDivisor T j hj).SequenceOfBlowups)
    (hpr : (MarkedBlowupSequenceData.ofMarkedSequence s).toBlowupSequenceData.CentersContainNoComponent)
    (hmk : (BlowupSequenceData.prepend (containedComponentsIdeal T j hj) hb
        (ambientBlowupSeq hres hno T j hj (lowerIdealAfterBlowup T j hj) (lowerBoundaryAfterBlowup T j hj) s hpr)).IsMarked
      T.structMap T.ideal T.mult T.boundary) :
    (prependedPushedMarkedSeq hres hno T j hj hb s hpr hmk).length = s.length + 1 := by
  have h1 : (BlowupSequenceData.prepend (containedComponentsIdeal T j hj) hb
      (ambientBlowupSeq hres hno T j hj (lowerIdealAfterBlowup T j hj) (lowerBoundaryAfterBlowup T j hj) s hpr)).length
      = s.length + 1 := by
    rw [BlowupSequenceData.prepend_length,
      ambientBlowupSeq_length hres hno T j hj (lowerIdealAfterBlowup T j hj) (lowerBoundaryAfterBlowup T j hj) s hpr]
  exact h1

private theorem prependedAmbientSeq_blowupMorphism (hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u})
    (hno : BlowupPreservesNoetherian.{u}) (T : MarkedIdealWithBoundary.{u})
    [AlgebraicGeometry.IsNoetherian T.scheme] (j : ℕ) (hj : j < T.boundary.length)
    (hb : Blowup.IsBlowupAlongIdealSheaf (𝟙 T.scheme) (containedComponentsIdeal T j hj))
    (s : (restrictTwistedToDivisor T j hj).SequenceOfBlowups)
    (hpr : (MarkedBlowupSequenceData.ofMarkedSequence s).toBlowupSequenceData.CentersContainNoComponent)
    (hmk : (BlowupSequenceData.prepend (containedComponentsIdeal T j hj) hb
        (ambientBlowupSeq hres hno T j hj (lowerIdealAfterBlowup T j hj) (lowerBoundaryAfterBlowup T j hj) s hpr)).IsMarked
      T.structMap T.ideal T.mult T.boundary) (n : ℕ) :
    (prependedPushedMarkedSeq hres hno T j hj hb s hpr hmk).transitionMapSucc n =
      (BlowupSequenceData.prepend (containedComponentsIdeal T j hj) hb
        (ambientBlowupSeq hres hno T j hj (lowerIdealAfterBlowup T j hj) (lowerBoundaryAfterBlowup T j hj) s hpr)).map n :=
  MarkedBlowupSequenceData.toMarkedSequence_blowupMorphism
    ((BlowupSequenceData.prepend (containedComponentsIdeal T j hj) hb
      (ambientBlowupSeq hres hno T j hj (lowerIdealAfterBlowup T j hj) (lowerBoundaryAfterBlowup T j hj) s hpr)).toMarkedBlowupSequenceData
      T.structMap T.ideal T.mult T.boundary hmk) n

private theorem prependedAmbientSeq_center (hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u})
    (hno : BlowupPreservesNoetherian.{u}) (T : MarkedIdealWithBoundary.{u})
    [AlgebraicGeometry.IsNoetherian T.scheme] (j : ℕ) (hj : j < T.boundary.length)
    (hb : Blowup.IsBlowupAlongIdealSheaf (𝟙 T.scheme) (containedComponentsIdeal T j hj))
    (s : (restrictTwistedToDivisor T j hj).SequenceOfBlowups)
    (hpr : (MarkedBlowupSequenceData.ofMarkedSequence s).toBlowupSequenceData.CentersContainNoComponent)
    (hmk : (BlowupSequenceData.prepend (containedComponentsIdeal T j hj) hb
        (ambientBlowupSeq hres hno T j hj (lowerIdealAfterBlowup T j hj) (lowerBoundaryAfterBlowup T j hj) s hpr)).IsMarked
      T.structMap T.ideal T.mult T.boundary) (n : ℕ) :
    (prependedPushedMarkedSeq hres hno T j hj hb s hpr hmk).center n =
      (BlowupSequenceData.prepend (containedComponentsIdeal T j hj) hb
        (ambientBlowupSeq hres hno T j hj (lowerIdealAfterBlowup T j hj) (lowerBoundaryAfterBlowup T j hj) s hpr)).center n :=
  MarkedBlowupSequenceData.toMarkedSequence_center
    ((BlowupSequenceData.prepend (containedComponentsIdeal T j hj) hb
      (ambientBlowupSeq hres hno T j hj (lowerIdealAfterBlowup T j hj) (lowerBoundaryAfterBlowup T j hj) s hpr)).toMarkedBlowupSequenceData
      T.structMap T.ideal T.mult T.boundary hmk) n

private theorem prependedAmbientSeq_blowupMorphism_zero (hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u})
    (hno : BlowupPreservesNoetherian.{u}) (T : MarkedIdealWithBoundary.{u})
    [AlgebraicGeometry.IsNoetherian T.scheme] (j : ℕ) (hj : j < T.boundary.length)
    (hb : Blowup.IsBlowupAlongIdealSheaf (𝟙 T.scheme) (containedComponentsIdeal T j hj))
    (s : (restrictTwistedToDivisor T j hj).SequenceOfBlowups)
    (hpr : (MarkedBlowupSequenceData.ofMarkedSequence s).toBlowupSequenceData.CentersContainNoComponent)
    (hmk : (BlowupSequenceData.prepend (containedComponentsIdeal T j hj) hb
        (ambientBlowupSeq hres hno T j hj (lowerIdealAfterBlowup T j hj) (lowerBoundaryAfterBlowup T j hj) s hpr)).IsMarked
      T.structMap T.ideal T.mult T.boundary) :
    (prependedPushedMarkedSeq hres hno T j hj hb s hpr hmk).transitionMapSucc 0 = 𝟙 T.scheme := by
  rw [prependedAmbientSeq_blowupMorphism hres hno T j hj hb s hpr hmk 0, BlowupSequenceData.prepend_blowupMorphism_zero]
  exact ambientBlowupSeq_isoObjZero_hom hres hno T j hj (lowerIdealAfterBlowup T j hj) (lowerBoundaryAfterBlowup T j hj) s hpr

private theorem prependedAmbientSeq_blowupMorphism_succ (hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u})
    (hno : BlowupPreservesNoetherian.{u}) (T : MarkedIdealWithBoundary.{u})
    [AlgebraicGeometry.IsNoetherian T.scheme] (j : ℕ) (hj : j < T.boundary.length)
    (hb : Blowup.IsBlowupAlongIdealSheaf (𝟙 T.scheme) (containedComponentsIdeal T j hj))
    (s : (restrictTwistedToDivisor T j hj).SequenceOfBlowups)
    (hpr : (MarkedBlowupSequenceData.ofMarkedSequence s).toBlowupSequenceData.CentersContainNoComponent)
    (hmk : (BlowupSequenceData.prepend (containedComponentsIdeal T j hj) hb
        (ambientBlowupSeq hres hno T j hj (lowerIdealAfterBlowup T j hj) (lowerBoundaryAfterBlowup T j hj) s hpr)).IsMarked
      T.structMap T.ideal T.mult T.boundary) (n : ℕ) :
    (prependedPushedMarkedSeq hres hno T j hj hb s hpr hmk).transitionMapSucc (n + 1) =
      (ambientBlowupSeq hres hno T j hj (lowerIdealAfterBlowup T j hj) (lowerBoundaryAfterBlowup T j hj) s hpr).map n :=
  (prependedAmbientSeq_blowupMorphism hres hno T j hj hb s hpr hmk (n + 1)).trans
    (BlowupSequenceData.prepend_blowupMorphism_succ (containedComponentsIdeal T j hj) hb
      (ambientBlowupSeq hres hno T j hj (lowerIdealAfterBlowup T j hj) (lowerBoundaryAfterBlowup T j hj) s hpr) n)

private theorem prependedAmbientSeq_center_zero (hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u})
    (hno : BlowupPreservesNoetherian.{u}) (T : MarkedIdealWithBoundary.{u})
    [AlgebraicGeometry.IsNoetherian T.scheme] (j : ℕ) (hj : j < T.boundary.length)
    (hb : Blowup.IsBlowupAlongIdealSheaf (𝟙 T.scheme) (containedComponentsIdeal T j hj))
    (s : (restrictTwistedToDivisor T j hj).SequenceOfBlowups)
    (hpr : (MarkedBlowupSequenceData.ofMarkedSequence s).toBlowupSequenceData.CentersContainNoComponent)
    (hmk : (BlowupSequenceData.prepend (containedComponentsIdeal T j hj) hb
        (ambientBlowupSeq hres hno T j hj (lowerIdealAfterBlowup T j hj) (lowerBoundaryAfterBlowup T j hj) s hpr)).IsMarked
      T.structMap T.ideal T.mult T.boundary) :
    (prependedPushedMarkedSeq hres hno T j hj hb s hpr hmk).center 0 = containedComponentsIdeal T j hj :=
  (prependedAmbientSeq_center hres hno T j hj hb s hpr hmk 0).trans
    (BlowupSequenceData.prepend_center_zero (containedComponentsIdeal T j hj) hb
      (ambientBlowupSeq hres hno T j hj (lowerIdealAfterBlowup T j hj) (lowerBoundaryAfterBlowup T j hj) s hpr))

private theorem prependedAmbientSeq_center_succ (hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u})
    (hno : BlowupPreservesNoetherian.{u}) (T : MarkedIdealWithBoundary.{u})
    [AlgebraicGeometry.IsNoetherian T.scheme] (j : ℕ) (hj : j < T.boundary.length)
    (hb : Blowup.IsBlowupAlongIdealSheaf (𝟙 T.scheme) (containedComponentsIdeal T j hj))
    (s : (restrictTwistedToDivisor T j hj).SequenceOfBlowups)
    (hpr : (MarkedBlowupSequenceData.ofMarkedSequence s).toBlowupSequenceData.CentersContainNoComponent)
    (hmk : (BlowupSequenceData.prepend (containedComponentsIdeal T j hj) hb
        (ambientBlowupSeq hres hno T j hj (lowerIdealAfterBlowup T j hj) (lowerBoundaryAfterBlowup T j hj) s hpr)).IsMarked
      T.structMap T.ideal T.mult T.boundary) (n : ℕ) :
    (prependedPushedMarkedSeq hres hno T j hj hb s hpr hmk).center (n + 1) =
      (ambientBlowupSeq hres hno T j hj (lowerIdealAfterBlowup T j hj) (lowerBoundaryAfterBlowup T j hj) s hpr).center n :=
  (prependedAmbientSeq_center hres hno T j hj hb s hpr hmk (n + 1)).trans
    (BlowupSequenceData.prepend_center_succ (containedComponentsIdeal T j hj) hb
      (ambientBlowupSeq hres hno T j hj (lowerIdealAfterBlowup T j hj) (lowerBoundaryAfterBlowup T j hj) s hpr) n)

private theorem prependedAmbientSeq_isoObjZero_hom (hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u})
    (hno : BlowupPreservesNoetherian.{u}) (T : MarkedIdealWithBoundary.{u})
    [AlgebraicGeometry.IsNoetherian T.scheme] (j : ℕ) (hj : j < T.boundary.length)
    (hb : Blowup.IsBlowupAlongIdealSheaf (𝟙 T.scheme) (containedComponentsIdeal T j hj))
    (s : (restrictTwistedToDivisor T j hj).SequenceOfBlowups)
    (hpr : (MarkedBlowupSequenceData.ofMarkedSequence s).toBlowupSequenceData.CentersContainNoComponent)
    (hmk : (BlowupSequenceData.prepend (containedComponentsIdeal T j hj) hb
        (ambientBlowupSeq hres hno T j hj (lowerIdealAfterBlowup T j hj) (lowerBoundaryAfterBlowup T j hj) s hpr)).IsMarked
      T.structMap T.ideal T.mult T.boundary) :
    (prependedPushedMarkedSeq hres hno T j hj hb s hpr hmk).isoZero.hom = 𝟙 T.scheme :=
  congrArg Iso.hom (BlowupSequenceData.prepend_isoObjZero (containedComponentsIdeal T j hj) hb
    (ambientBlowupSeq hres hno T j hj (lowerIdealAfterBlowup T j hj) (lowerBoundaryAfterBlowup T j hj) s hpr))

private theorem prependedAmbientSeq_projectionToSpec_succ (hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u})
    (hno : BlowupPreservesNoetherian.{u}) (T : MarkedIdealWithBoundary.{u})
    [AlgebraicGeometry.IsNoetherian T.scheme] (j : ℕ) (hj : j < T.boundary.length)
    (hb : Blowup.IsBlowupAlongIdealSheaf (𝟙 T.scheme) (containedComponentsIdeal T j hj))
    (s : (restrictTwistedToDivisor T j hj).SequenceOfBlowups)
    (hpr : (MarkedBlowupSequenceData.ofMarkedSequence s).toBlowupSequenceData.CentersContainNoComponent)
    (hmk : (BlowupSequenceData.prepend (containedComponentsIdeal T j hj) hb
        (ambientBlowupSeq hres hno T j hj (lowerIdealAfterBlowup T j hj) (lowerBoundaryAfterBlowup T j hj) s hpr)).IsMarked
      T.structMap T.ideal T.mult T.boundary) (n : ℕ) :
    (prependedPushedMarkedSeq hres hno T j hj hb s hpr hmk).projectionToSpec (n + 1) =
      (ambientBlowupSeq hres hno T j hj (lowerIdealAfterBlowup T j hj) (lowerBoundaryAfterBlowup T j hj) s hpr).projectionToBase n ≫
        T.structMap := by
  have h1 := MarkedBlowupSequenceData.toMarkedSequence_projectionToSpec
    ((BlowupSequenceData.prepend (containedComponentsIdeal T j hj) hb
      (ambientBlowupSeq hres hno T j hj (lowerIdealAfterBlowup T j hj) (lowerBoundaryAfterBlowup T j hj) s hpr)).toMarkedBlowupSequenceData
      T.structMap T.ideal T.mult T.boundary hmk) (n + 1)
  have h2 := BlowupSequenceData.projectionToBase_prepend_succ (containedComponentsIdeal T j hj) hb
    (ambientBlowupSeq hres hno T j hj (lowerIdealAfterBlowup T j hj) (lowerBoundaryAfterBlowup T j hj) s hpr) n
  exact h1.trans (congrArg (fun f => f ≫ T.structMap) h2)

private theorem ker_embeddingIntoAmbient_zero (hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u})
    (hno : BlowupPreservesNoetherian.{u}) (T : MarkedIdealWithBoundary.{u})
    [AlgebraicGeometry.IsNoetherian T.scheme] (j : ℕ) (hj : j < T.boundary.length)
    (hb : Blowup.IsBlowupAlongIdealSheaf (𝟙 T.scheme) (containedComponentsIdeal T j hj))
    (s : (restrictTwistedToDivisor T j hj).SequenceOfBlowups)
    (hpr : (MarkedBlowupSequenceData.ofMarkedSequence s).toBlowupSequenceData.CentersContainNoComponent)
    (hmk : (BlowupSequenceData.prepend (containedComponentsIdeal T j hj) hb
        (ambientBlowupSeq hres hno T j hj (lowerIdealAfterBlowup T j hj) (lowerBoundaryAfterBlowup T j hj) s hpr)).IsMarked
      T.structMap T.ideal T.mult T.boundary) :
    AlgebraicGeometry.Scheme.Hom.ker
        (embeddingIntoAmbient hres hno T j hj (lowerIdealAfterBlowup T j hj) (lowerBoundaryAfterBlowup T j hj) s hpr 0)
      = T.boundary.get ⟨j, hj⟩ := by
  have h2 := ker_embeddingIntoAmbient_zero_eq_comap_blowupMorphism hres hno T j hj hb s hpr hmk
  rw [prependedAmbientSeq_isoObjZero_hom hres hno T j hj hb s hpr hmk,
    prependedAmbientSeq_blowupMorphism_zero hres hno T j hj hb s hpr hmk] at h2
  have h3 : ((T.boundary.get ⟨j, hj⟩).comap (𝟙 T.scheme)).comap (𝟙 T.scheme)
      = T.boundary.get ⟨j, hj⟩ := by
    rw [Scheme.IdealSheafData.comap_id, Scheme.IdealSheafData.comap_id]
  exact h2.trans h3

private theorem isSmoothDivisor_prependedAmbientSeq_boundary_get (hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u})
    (hno : BlowupPreservesNoetherian.{u}) (T : MarkedIdealWithBoundary.{u})
    [AlgebraicGeometry.IsNoetherian T.scheme] (hV : T.IsAdmissible) (j : ℕ)
    (hj : j < T.boundary.length)
    (hb : Blowup.IsBlowupAlongIdealSheaf (𝟙 T.scheme) (containedComponentsIdeal T j hj))
    (s : (restrictTwistedToDivisor T j hj).SequenceOfBlowups)
    (hpr : (MarkedBlowupSequenceData.ofMarkedSequence s).toBlowupSequenceData.CentersContainNoComponent)
    (hmk : (BlowupSequenceData.prepend (containedComponentsIdeal T j hj) hb
        (ambientBlowupSeq hres hno T j hj (lowerIdealAfterBlowup T j hj) (lowerBoundaryAfterBlowup T j hj) s hpr)).IsMarked
      T.structMap T.ideal T.mult T.boundary)
    (i : ℕ) (hi : i ≤ s.length + 1)
    (h : j < ((prependedPushedMarkedSeq hres hno T j hj hb s hpr hmk).boundary i).length) :
    IsSmoothDivisor ((prependedPushedMarkedSeq hres hno T j hj hb s hpr hmk).projectionToSpec i)
      (((prependedPushedMarkedSeq hres hno T j hj hb s hpr hmk).boundary i).get ⟨j, h⟩) := by
  have hvl : (T.transformAt (prependedPushedMarkedSeq hres hno T j hj hb s hpr hmk) i).IsAdmissible :=
    MarkedIdealWithBoundary.IsAdmissible.transformAt effectiveCartierSupportContainsNoComponent hV
      (prependedPushedMarkedSeq hres hno T j hj hb s hpr hmk) i
      (by rw [prependedAmbientSeq_length hres hno T j hj hb s hpr hmk]; omega)
  have h2 : j < (T.transformAt (prependedPushedMarkedSeq hres hno T j hj hb s hpr hmk) i).boundary.length := by
    rw [MarkedIdealWithBoundary.transformAt_boundary]
    exact h
  have h3 := isSmoothDivisor_boundary_get
    (T.transformAt (prependedPushedMarkedSeq hres hno T j hj hb s hpr hmk) i) hvl j h2
  rw [MarkedIdealWithBoundary.transformAt_structureMorphism] at h3
  exact h3

private theorem prependedAmbientSeq_boundary_succ_get
    (hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u})
    (hno : BlowupPreservesNoetherian.{u}) (T : MarkedIdealWithBoundary.{u})
    [AlgebraicGeometry.IsNoetherian T.scheme] (j : ℕ) (hj : j < T.boundary.length)
    (hb : Blowup.IsBlowupAlongIdealSheaf (𝟙 T.scheme) (containedComponentsIdeal T j hj))
    (s : (restrictTwistedToDivisor T j hj).SequenceOfBlowups)
    (hpr : (MarkedBlowupSequenceData.ofMarkedSequence s).toBlowupSequenceData.CentersContainNoComponent)
    (hmk : (BlowupSequenceData.prepend (containedComponentsIdeal T j hj) hb
        (ambientBlowupSeq hres hno T j hj (lowerIdealAfterBlowup T j hj) (lowerBoundaryAfterBlowup T j hj) s hpr)).IsMarked
      T.structMap T.ideal T.mult T.boundary) :
    ∀ n, n ≤ s.length →
      ∀ h : j < ((prependedPushedMarkedSeq hres hno T j hj hb s hpr hmk).boundary (n + 1)).length,
        ((prependedPushedMarkedSeq hres hno T j hj hb s hpr hmk).boundary (n + 1)).get ⟨j, h⟩ =
          iteratedStrictTransform
            (ambientBlowupSeq hres hno T j hj (lowerIdealAfterBlowup T j hj) (lowerBoundaryAfterBlowup T j hj) s hpr)
            (Blowup.strictTransform (𝟙 T.scheme) (containedComponentsIdeal T j hj)
              ((T.boundary.get ⟨j, hj⟩).comap (𝟙 T.scheme))) n := by
  intro n
  induction n with
  | zero =>
    intro _ h
    have hz0 : j < ((prependedPushedMarkedSeq hres hno T j hj hb s hpr hmk).boundary 0).length :=
      lt_of_lt_of_le hj
        (length_le_length_boundary (prependedPushedMarkedSeq hres hno T j hj hb s hpr hmk) 0 (Nat.zero_le _))
    rw [boundary_succ_get_eq_strictTransform (prependedPushedMarkedSeq hres hno T j hj hb s hpr hmk) j 0
        (by rw [prependedAmbientSeq_length hres hno T j hj hb s hpr hmk]; omega) hz0 h,
      boundary_zero_get_eq_comap (prependedPushedMarkedSeq hres hno T j hj hb s hpr hmk) j hj hz0,
      prependedAmbientSeq_isoObjZero_hom hres hno T j hj hb s hpr hmk,
      prependedAmbientSeq_blowupMorphism_zero hres hno T j hj hb s hpr hmk,
      prependedAmbientSeq_center_zero hres hno T j hj hb s hpr hmk]
    rfl
  | succ n ih =>
    intro hn h
    have hn1 : j < ((prependedPushedMarkedSeq hres hno T j hj hb s hpr hmk).boundary (n + 1)).length :=
      lt_of_lt_of_le hj (length_le_length_boundary (prependedPushedMarkedSeq hres hno T j hj hb s hpr hmk) (n + 1)
        (by rw [prependedAmbientSeq_length hres hno T j hj hb s hpr hmk]; omega))
    rw [boundary_succ_get_eq_strictTransform (prependedPushedMarkedSeq hres hno T j hj hb s hpr hmk) j (n + 1)
        (by rw [prependedAmbientSeq_length hres hno T j hj hb s hpr hmk]; omega) hn1 h,
      ih (by omega) hn1,
      prependedAmbientSeq_blowupMorphism_succ hres hno T j hj hb s hpr hmk n,
      prependedAmbientSeq_center_succ hres hno T j hj hb s hpr hmk n]
    rfl

private theorem projectionToBase_mem_support_of_mem_support_ideal (T : MarkedIdealWithBoundary.{u}) (j : ℕ)
    (hj : j < T.boundary.length) (s : (restrictTwistedToDivisor T j hj).SequenceOfBlowups) :
    ∀ n, n ≤ s.length → ∀ y : ↥((MarkedBlowupSequenceData.ofMarkedSequence s).obj n),
      y ∈ (↑((MarkedBlowupSequenceData.ofMarkedSequence s).ideal n).support :
          Set ↥((MarkedBlowupSequenceData.ofMarkedSequence s).obj n)) →
      (MarkedBlowupSequenceData.ofMarkedSequence s).proj n y ∈
        (↑(restrictTwistedToDivisor T j hj).ideal.support : Set ↥(restrictTwistedToDivisor T j hj).scheme) := by
  intro n
  induction n with
  | zero =>
    intro _ y hy
    have h1 : (MarkedBlowupSequenceData.ofMarkedSequence s).ideal 0
        = (restrictTwistedToDivisor T j hj).ideal.comap (MarkedBlowupSequenceData.ofMarkedSequence s).isoZero.hom :=
      (MarkedBlowupSequenceData.ofMarkedSequence s).ideal_zero
    rw [h1] at hy
    have h2 : (MarkedBlowupSequenceData.ofMarkedSequence s).isoZero.hom y ∈
        (↑(restrictTwistedToDivisor T j hj).ideal.support : Set ↥(restrictTwistedToDivisor T j hj).scheme) :=
      Scheme.IdealSheafData.mem_support_comap.mp hy
    have h3 : (MarkedBlowupSequenceData.ofMarkedSequence s).proj 0
        = (MarkedBlowupSequenceData.ofMarkedSequence s).isoZero.hom :=
      (MarkedBlowupSequenceData.ofMarkedSequence s).proj_zero
    rw [h3]
    exact h2
  | succ n ih =>
    intro hn y hy
    have hn' : n < (MarkedBlowupSequenceData.ofMarkedSequence s).length := by
      rw [MarkedBlowupSequenceData.ofMarkedSequence_length]
      omega
    have h2 := (MarkedBlowupSequenceData.ofMarkedSequence s).ideal_succ n hn'
    have h1 : (1 : ℕ∞) ≤ orderAt ((MarkedBlowupSequenceData.ofMarkedSequence s).ideal (n + 1)) y :=
      (one_le_orderAt_iff_mem_support _ _).2 hy
    have h5 : orderAt (Blowup.exceptionalIdeal ((MarkedBlowupSequenceData.ofMarkedSequence s).map n)
            ((MarkedBlowupSequenceData.ofMarkedSequence s).center n) ^ (restrictTwistedToDivisor T j hj).mult) y
          + orderAt ((MarkedBlowupSequenceData.ofMarkedSequence s).ideal (n + 1)) y
        ≤ orderAt (Blowup.exceptionalIdeal ((MarkedBlowupSequenceData.ofMarkedSequence s).map n)
            ((MarkedBlowupSequenceData.ofMarkedSequence s).center n) ^ (restrictTwistedToDivisor T j hj).mult
            * (MarkedBlowupSequenceData.ofMarkedSequence s).ideal (n + 1)) y := by
      apply add_orderAt_le_orderAt_mul
    rw [h2] at h5
    have h6 : (1 : ℕ∞) ≤ orderAt (((MarkedBlowupSequenceData.ofMarkedSequence s).ideal n).comap
        ((MarkedBlowupSequenceData.ofMarkedSequence s).map n)) y :=
      le_trans (le_trans h1 le_add_self) h5
    have h7 : y ∈ (↑(((MarkedBlowupSequenceData.ofMarkedSequence s).ideal n).comap
        ((MarkedBlowupSequenceData.ofMarkedSequence s).map n)).support :
          Set ↥((MarkedBlowupSequenceData.ofMarkedSequence s).obj (n + 1))) :=
      (one_le_orderAt_iff_mem_support _ _).1 h6
    have h8 : (MarkedBlowupSequenceData.ofMarkedSequence s).map n y ∈
        (↑((MarkedBlowupSequenceData.ofMarkedSequence s).ideal n).support :
          Set ↥((MarkedBlowupSequenceData.ofMarkedSequence s).obj n)) :=
      Scheme.IdealSheafData.mem_support_comap.mp h7
    have h9 := ih (by omega) _ h8
    have h10 : (MarkedBlowupSequenceData.ofMarkedSequence s).proj (n + 1)
        = (MarkedBlowupSequenceData.ofMarkedSequence s).map n ≫ (MarkedBlowupSequenceData.ofMarkedSequence s).proj n :=
      (MarkedBlowupSequenceData.ofMarkedSequence s).proj_succ n
    rw [h10]
    exact h9

private theorem disjoint_support_center_iteratedComap_containedComponentsIdeal
    (hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u})
    (hno : BlowupPreservesNoetherian.{u}) (T : MarkedIdealWithBoundary.{u})
    [AlgebraicGeometry.IsNoetherian T.scheme] (hV : T.IsAdmissible)
    (hord : ∀ x : ↥T.scheme, orderAt T.ideal x ≤ (T.mult : ℕ∞))
    (j : ℕ) (hj : j < T.boundary.length) (hlow : (restrictTwistedToDivisor T j hj).IsAdmissible)
    (s : (restrictTwistedToDivisor T j hj).SequenceOfBlowups)
    (hpr : (MarkedBlowupSequenceData.ofMarkedSequence s).toBlowupSequenceData.CentersContainNoComponent)
    (hcomp : ∀ t ≤ s.length,
      embeddingIntoAmbient hres hno T j hj (lowerIdealAfterBlowup T j hj) (lowerBoundaryAfterBlowup T j hj) s hpr t ≫
          (ambientBlowupSeq hres hno T j hj (lowerIdealAfterBlowup T j hj) (lowerBoundaryAfterBlowup T j hj) s hpr).projectionToBase t =
        (MarkedBlowupSequenceData.ofMarkedSequence s).proj t ≫ (T.boundary.get ⟨j, hj⟩).subschemeι)
    (n : ℕ) (hn : n < s.length) :
    Disjoint
      (↑((ambientBlowupSeq hres hno T j hj (lowerIdealAfterBlowup T j hj)
          (lowerBoundaryAfterBlowup T j hj) s hpr).center n).support :
        Set ↥((ambientBlowupSeq hres hno T j hj (lowerIdealAfterBlowup T j hj) (lowerBoundaryAfterBlowup T j hj) s hpr).obj n))
      (↑(TransportedDivisor.iteratedComap
          (ambientBlowupSeq hres hno T j hj (lowerIdealAfterBlowup T j hj) (lowerBoundaryAfterBlowup T j hj) s hpr)
          (containedComponentsIdeal T j hj) n).support :
        Set ↥((ambientBlowupSeq hres hno T j hj (lowerIdealAfterBlowup T j hj)
          (lowerBoundaryAfterBlowup T j hj) s hpr).obj n)) := by
  rw [Set.disjoint_left]
  intro y hy1 hy2
  rw [support_ambientBlowupSeq_center_eq_image hres hno T j hj (lowerIdealAfterBlowup T j hj)
    (lowerBoundaryAfterBlowup T j hj) s hpr n] at hy1
  obtain ⟨z, hz, rfl⟩ := hy1
  have hn' : n < (MarkedBlowupSequenceData.ofMarkedSequence s).length := by
    rw [MarkedBlowupSequenceData.ofMarkedSequence_length]
    exact hn
  have hzco := (MarkedBlowupSequenceData.ofMarkedSequence s).center_order n hn' hz
  rw [mem_orderAtLeastLocus_iff] at hzco
  have hz2 : (1 : ℕ∞) ≤ orderAt ((MarkedBlowupSequenceData.ofMarkedSequence s).ideal n) z :=
    le_trans (by exact_mod_cast hlow.one_le_mult) hzco
  have hzs : z ∈ (↑((MarkedBlowupSequenceData.ofMarkedSequence s).ideal n).support :
      Set ↥((MarkedBlowupSequenceData.ofMarkedSequence s).obj n)) :=
    (one_le_orderAt_iff_mem_support _ _).1 hz2
  have hw1 := projectionToBase_mem_support_of_mem_support_ideal T j hj s n (le_of_lt hn) z hzs
  have hw2 : (T.boundary.get ⟨j, hj⟩).subschemeι ((MarkedBlowupSequenceData.ofMarkedSequence s).proj n z)
      ∈ (↑(lowerIdealAfterBlowup T j hj).support : Set ↥T.scheme) :=
    Scheme.IdealSheafData.mem_support_comap.mp hw1
  have hsupp := TransportedDivisor.support_iteratedComap
      (ambientBlowupSeq hres hno T j hj (lowerIdealAfterBlowup T j hj) (lowerBoundaryAfterBlowup T j hj) s hpr)
      (containedComponentsIdeal T j hj) n
  rw [ambientBlowupSeq_projectionToBase_comp_isoObjZero_inv hres hno T j hj (lowerIdealAfterBlowup T j hj)
    (lowerBoundaryAfterBlowup T j hj) s hpr n] at hsupp
  rw [hsupp] at hy2
  have hz' : z ∈ ⇑(embeddingIntoAmbient hres hno T j hj (lowerIdealAfterBlowup T j hj)
        (lowerBoundaryAfterBlowup T j hj) s hpr n ≫
      (ambientBlowupSeq hres hno T j hj (lowerIdealAfterBlowup T j hj) (lowerBoundaryAfterBlowup T j hj) s hpr).projectionToBase n) ⁻¹'
      (↑(containedComponentsIdeal T j hj).support : Set ↥T.scheme) := hy2
  rw [hcomp n (le_of_lt hn)] at hz'
  exact (Set.disjoint_left.1
    (disjoint_support_lowerIdealAfterBlowup_containedComponentsIdeal T hV hord j hj)) hw2 hz'

theorem isSmoothDivisor_ker_embeddingIntoAmbient (hres : FunctorialResolution.Blowup.StrictTransformIsBlowupOfClosedSubscheme.{u})
    (hno : BlowupPreservesNoetherian.{u}) (_hgeom : OrderAtComapOffExceptionalLocus.{u})
    (T : MarkedIdealWithBoundary.{u}) [AlgebraicGeometry.IsNoetherian T.scheme] (hV : T.IsAdmissible)
    (hord : ∀ x : ↥T.scheme, orderAt T.ideal x ≤ (T.mult : ℕ∞))
    (j : ℕ) (hj : j < T.boundary.length)
    (hb : Blowup.IsBlowupAlongIdealSheaf (𝟙 T.scheme) (containedComponentsIdeal T j hj))
    (hlow : (restrictTwistedToDivisor T j hj).IsAdmissible)
    (s : (restrictTwistedToDivisor T j hj).SequenceOfBlowups)
    (hpr : (MarkedBlowupSequenceData.ofMarkedSequence s).toBlowupSequenceData.CentersContainNoComponent)
    (hmk : (BlowupSequenceData.prepend (containedComponentsIdeal T j hj) hb
        (ambientBlowupSeq hres hno T j hj (lowerIdealAfterBlowup T j hj) (lowerBoundaryAfterBlowup T j hj) s hpr)).IsMarked
      T.structMap T.ideal T.mult T.boundary)
    (hcomp : ∀ t ≤ s.length,
      embeddingIntoAmbient hres hno T j hj (lowerIdealAfterBlowup T j hj) (lowerBoundaryAfterBlowup T j hj) s hpr t ≫
          (ambientBlowupSeq hres hno T j hj (lowerIdealAfterBlowup T j hj) (lowerBoundaryAfterBlowup T j hj) s hpr).projectionToBase t =
        (MarkedBlowupSequenceData.ofMarkedSequence s).proj t ≫ (T.boundary.get ⟨j, hj⟩).subschemeι) :
    ∀ t ≤ s.length,
      IsSmoothDivisor ((prependedPushedMarkedSeq hres hno T j hj hb s hpr hmk).projectionToSpec (t + 1))
        (AlgebraicGeometry.Scheme.Hom.ker
          (embeddingIntoAmbient hres hno T j hj (lowerIdealAfterBlowup T j hj) (lowerBoundaryAfterBlowup T j hj) s hpr t)) := by
  classical
  have := hV.charZero
  have := hV.smooth
  have hL : s.length ≤ (ambientBlowupSeq hres hno T j hj (lowerIdealAfterBlowup T j hj)
      (lowerBoundaryAfterBlowup T j hj) s hpr).length :=
    le_of_eq (ambientBlowupSeq_length hres hno T j hj (lowerIdealAfterBlowup T j hj)
      (lowerBoundaryAfterBlowup T j hj) s hpr).symm
  have hnoeth : ∀ t, t ≤ s.length → IsLocallyNoetherian
      ((ambientBlowupSeq hres hno T j hj (lowerIdealAfterBlowup T j hj) (lowerBoundaryAfterBlowup T j hj) s hpr).obj t) := by
    intro t htt
    have : AlgebraicGeometry.IsNoetherian
        ((ambientBlowupSeq hres hno T j hj (lowerIdealAfterBlowup T j hj) (lowerBoundaryAfterBlowup T j hj) s hpr).obj t) :=
      isNoetherian_ambientBlowupSequence_schemeAt (T.boundary.get ⟨j, hj⟩).subschemeι
        (MarkedBlowupSequenceData.ofMarkedSequence s).toBlowupSequenceData hres hno hpr t
        (le_of_le_of_eq htt (MarkedBlowupSequenceData.ofMarkedSequence_length s).symm)
    infer_instance
  have hsm : ∀ t, t ≤ s.length → AlgebraicGeometry.Smooth
      ((ambientBlowupSeq hres hno T j hj (lowerIdealAfterBlowup T j hj) (lowerBoundaryAfterBlowup T j hj) s hpr).projectionToBase t ≫
        T.structMap) := by
    intro t htt
    have h1 := MarkedSequenceOfBlowups.smooth_projectionToSpec effectiveCartierSupportContainsNoComponent hV
      (prependedPushedMarkedSeq hres hno T j hj hb s hpr hmk) (t + 1)
      (by rw [prependedAmbientSeq_length hres hno T j hj hb s hpr hmk]; omega)
    rw [prependedAmbientSeq_projectionToSpec_succ hres hno T j hj hb s hpr hmk t] at h1
    exact h1
  intro t ht
  rw [prependedAmbientSeq_projectionToSpec_succ hres hno T j hj hb s hpr hmk t]
  refine TransportedDivisor.isSmoothDivisor_strictTransform_of_disjoint_center T.structMap
    (ambientBlowupSeq hres hno T j hj (lowerIdealAfterBlowup T j hj) (lowerBoundaryAfterBlowup T j hj) s hpr)
    s.length hL hnoeth hsm
    (fun n => AlgebraicGeometry.Scheme.Hom.ker
      (embeddingIntoAmbient hres hno T j hj (lowerIdealAfterBlowup T j hj) (lowerBoundaryAfterBlowup T j hj) s hpr n))
    (iteratedStrictTransform
      (ambientBlowupSeq hres hno T j hj (lowerIdealAfterBlowup T j hj) (lowerBoundaryAfterBlowup T j hj) s hpr)
      (Blowup.strictTransform (𝟙 T.scheme) (containedComponentsIdeal T j hj)
        ((T.boundary.get ⟨j, hj⟩).comap (𝟙 T.scheme))))
    (containedComponentsIdeal T j hj) ?_ ?_ ?_ ?_ ?_ ?_ ?_ t ht
  · rw [ker_embeddingIntoAmbient_zero hres hno T j hj hb s hpr hmk]
    exact (DivisorReductionBoundary.strictTransform_mul_containedComponentsIdeal T hV j hj).symm
  · exact DivisorReductionBoundary.disjoint_support_strictTransform_containedComponentsIdeal T hV j hj
  · intro n hn
    exact ker_embeddingIntoAmbientBlowupSequence_succ (T.boundary.get ⟨j, hj⟩).subschemeι
      (MarkedBlowupSequenceData.ofMarkedSequence s).toBlowupSequenceData hres hno hpr n
      (by rw [MarkedBlowupSequenceData.ofMarkedSequence_length]; exact hn)
  · intro n _
    exact strictTransformIter_succ _ _ n
  · rw [ambientBlowupSeq_projectionToBase_zero_comp_structureMorphism hres hno T j hj (lowerIdealAfterBlowup T j hj)
      (lowerBoundaryAfterBlowup T j hj) s hpr]
    exact DivisorReductionBoundary.isSmoothDivisor_containedComponentsIdeal T hV j hj
  · intro n hn
    have hlt : j < ((prependedPushedMarkedSeq hres hno T j hj hb s hpr hmk).boundary (n + 1)).length :=
      lt_of_lt_of_le hj (length_le_length_boundary (prependedPushedMarkedSeq hres hno T j hj hb s hpr hmk) (n + 1)
        (by rw [prependedAmbientSeq_length hres hno T j hj hb s hpr hmk]; omega))
    have h1 := isSmoothDivisor_prependedAmbientSeq_boundary_get hres hno T hV j hj hb s hpr hmk (n + 1)
      (by omega) hlt
    rw [prependedAmbientSeq_boundary_succ_get hres hno T j hj hb s hpr hmk n hn hlt,
      prependedAmbientSeq_projectionToSpec_succ hres hno T j hj hb s hpr hmk n] at h1
    exact h1
  · intro n hn
    exact disjoint_support_center_iteratedComap_containedComponentsIdeal hres hno T hV hord j hj
      hlow s hpr hcomp n hn

end DivisorReduction

end FunctorialResolution.EmbeddedResolution

end
