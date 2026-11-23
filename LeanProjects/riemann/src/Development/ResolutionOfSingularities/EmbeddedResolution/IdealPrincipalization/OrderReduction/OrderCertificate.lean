import Mathlib
import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.BlowupSequenceRelations
import Development.ResolutionOfSingularities.Foundations.Blowup.StrictTransform
import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.IdealSheafOrder
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.PullbackBlowupSequenceComposition
import Development.ResolutionOfSingularities.EmbeddedResolution.MaximalContactHypersurfaces.TunedSheaf
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReductionProperties
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.PrincipalizationCertificateMonotone
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.PrincipalizationCertificate
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.MaxContactReduction
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.MaxContactResolution
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.DescentHypotheses
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.DerivedAndCoverTriples
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.StrictPullbackBlowupSeq
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.BlowupSequenceData
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.Append
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.ControlledTransform
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.IdealBlowupSequence
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.MarkedSequenceOfBlowups
import Development.ResolutionOfSingularities.Foundations.BlowupUniversalProperty
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionOfSingularities
universe u

open CategoryTheory AlgebraicGeometry

namespace FunctorialResolution.EmbeddedResolution

private theorem orderCertificate_congr_mult {k : Type u} [Field k] {W : Scheme.{u}}
    {p : W ⟶ Spec (CommRingCat.of k)} {N : W.IdealSheafData} {μ μ' : ℕ}
    {Mem : Set ↥W} {Z : W.IdealSheafData} (h : μ = μ')
    (c : OrderCertificate W p N μ Mem Z) : OrderCertificate W p N μ' Mem Z := by
  subst h
  exact c

private theorem orderCertificate_congr_map {k : Type u} [Field k] {W : Scheme.{u}}
    {p p' : W ⟶ Spec (CommRingCat.of k)} {N : W.IdealSheafData} {μ : ℕ}
    {Mem : Set ↥W} {Z : W.IdealSheafData} (h : p = p')
    (c : OrderCertificate W p N μ Mem Z) : OrderCertificate W p' N μ Mem Z := by
  subst h
  exact c

private theorem boundaryLocus_eq_iUnion_support {k : Type u} [Field k] {X : Scheme.{u}}
    {p : X ⟶ Spec (CommRingCat.of k)} {I : X.IdealSheafData} {m : ℕ}
    {E : List X.IdealSheafData} (s : MarkedSequenceOfBlowups p I m E) (t : ℕ) :
    MarkedSequenceOfBlowups.boundaryLocus s t
      = ⋃ D ∈ s.boundary t, (↑D.support : Set ↥(s.schemeAt t)) := by
  ext x
  rw [MarkedSequenceOfBlowups.mem_boundaryLocus_iff]
  constructor
  · rintro ⟨D, hD, hx⟩
    exact Set.mem_iUnion₂.2 ⟨D, hD, hx⟩
  · intro hx
    obtain ⟨D, hD, hx⟩ := Set.mem_iUnion₂.1 hx
    exact ⟨D, hD, hx⟩

private theorem boundary_eq_map_comap_strictPullbackComparisonMap_of_flat {k : Type u} [Field k] {X' X : Scheme.{u}}
    {q : X' ⟶ Spec (CommRingCat.of k)} {g : X' ⟶ X} {I : X.IdealSheafData} {m : ℕ}
    {E : List X.IdealSheafData} {d : BlowupSequenceData X}
    (hf : AlgebraicGeometry.Flat g)
    (s : MarkedBlowupSequenceData q (I.comap g) m (List.map (fun A => A.comap g) E))
    (D : StrictPullbackBlowupSeq g s.toMarkedSequenceOfBlowups.toSequenceOfBlowups d.toSequenceOfBlowups)
    (hNd : ∀ i ≤ d.length, AlgebraicGeometry.IsLocallyNoetherian (d.obj i))
    (hNt : ∀ i ≤ s.length, AlgebraicGeometry.IsLocallyNoetherian (s.obj i))
    (i : ℕ) (hi : i ≤ s.length) :
    s.boundary i = List.map (fun A => A.comap (s.strictPullbackComparisonMap D i hi)) (d.boundaryFrom E i) := by
  have := hf
  exact MarkedBlowupSequenceData.boundary_eq_comap_strictPullbackComparisonMap s D hNd hNt i hi

private theorem surjective_strictPullbackComparisonMap_of_flat_of_surjective {k : Type u} [Field k] {X' X : Scheme.{u}}
    {q : X' ⟶ Spec (CommRingCat.of k)} {g : X' ⟶ X} {I : X.IdealSheafData} {m : ℕ}
    {E : List X.IdealSheafData} {d : BlowupSequenceData X}
    (hf : AlgebraicGeometry.Flat g) (hs : AlgebraicGeometry.Surjective g)
    (s : MarkedBlowupSequenceData q (I.comap g) m (List.map (fun A => A.comap g) E))
    (D : StrictPullbackBlowupSeq g s.toMarkedSequenceOfBlowups.toSequenceOfBlowups d.toSequenceOfBlowups)
    (i : ℕ) (hi : i ≤ s.length) :
    AlgebraicGeometry.Surjective (s.strictPullbackComparisonMap D i hi) := by
  have := hf
  have := hs
  exact MarkedBlowupSequenceData.surjective_strictPullbackComparisonMap s D i hi

theorem iUnion_support_comap_eq_preimage {X Y : Scheme.{u}} (f : X ⟶ Y)
    (l : List Y.IdealSheafData) :
    (⋃ J ∈ l.map (fun D => D.comap f), (↑J.support : Set ↥X)) =
      (⇑f) ⁻¹' (⋃ J ∈ l, (↑J.support : Set ↥Y)) := by
  ext x
  constructor
  · intro hx
    obtain ⟨J, hJ, hx⟩ := Set.mem_iUnion₂.1 hx
    obtain ⟨D, hD, rfl⟩ := List.mem_map.1 hJ
    exact Set.mem_preimage.2 (Set.mem_iUnion₂.2
      ⟨D, hD, (AlgebraicGeometry.Scheme.IdealSheafData.mem_support_comap ..).mp hx⟩)
  · intro hx
    obtain ⟨D, hD, hx⟩ := Set.mem_iUnion₂.1 (Set.mem_preimage.1 hx)
    exact Set.mem_iUnion₂.2
      ⟨D.comap f, List.mem_map.2 ⟨D, hD, rfl⟩,
        (AlgebraicGeometry.Scheme.IdealSheafData.mem_support_comap ..).mpr hx⟩

namespace MaxContactFunctoriality

private theorem mem_boundary_of_forall_mem {X : Scheme.{u}} (d : BlowupSequenceData X)
    (E E' : List X.IdealSheafData) (hEE : ∀ D ∈ E, D ∈ E') :
    ∀ (t : ℕ) (D : (d.obj t).IdealSheafData), D ∈ d.boundaryFrom E t → D ∈ d.boundaryFrom E' t := by
  intro t
  induction t with
  | zero =>
      intro D hD
      rw [BlowupSequenceData.boundary_zero] at hD ⊢
      obtain ⟨A, hA, rfl⟩ := List.mem_map.1 hD
      exact List.mem_map.2 ⟨A, hEE A hA, rfl⟩
  | succ t ih =>
      intro D hD
      rw [BlowupSequenceData.boundary_succ] at hD ⊢
      rcases List.mem_append.1 hD with hmem | hmem
      · obtain ⟨A, hA, rfl⟩ := List.mem_map.1 hmem
        exact List.mem_append.2 (Or.inl (List.mem_map.2 ⟨A, ih A hA, rfl⟩))
      · exact List.mem_append.2 (Or.inr hmem)

theorem mem_boundary_of_mem_boundary_dropTrivialBoundary (T : MarkedIdealWithBoundary.{u}) (d : BlowupSequenceData T.scheme) (t : ℕ)
    (D : (d.obj t).IdealSheafData)
    (hD : D ∈ d.boundaryFrom (MaxContactReduction.dropTrivialBoundary T).boundary t) :
    D ∈ d.boundaryFrom T.boundary t := by
  refine mem_boundary_of_forall_mem d _ _ ?_ t D hD
  intro A hA
  rw [MaxContactReduction.dropTrivialBoundary_boundary] at hA
  exact (List.mem_filter.1 hA).1

section

variable (hinv : ComapIsoInvariance.{u}) (P : ℕ → Prop) (A : ℕ → PrincipalizationAssignment.{u})
  (B : PrincipalizationAssignment.{u})

theorem orderCertificate_of_isStrictPullbackBlowupSeq (hstar : CoverSequenceProperties hinv P A) (hd : DescentHypotheses hinv P A B)
    (T : MarkedIdealWithBoundary.{u}) (h : OrderReductionHypotheses P T) (hone : T.mult = 1)
    (d : BlowupSequenceData T.scheme)
    (hmk : d.IsMarked T.structMap T.ideal T.mult T.boundary)
    (hpb : IsStrictPullbackBlowupSeq (MaxContactCoverData.coverMap T h.valid)
      (MaxContactCoverData.coverMarkedBlowupData T h.valid hinv (lowerDimensionalFamily A T)).toSequenceOfBlowups d.toSequenceOfBlowups)
    (t : ℕ) (ht : t < d.length) :
    OrderCertificate ((d.toMarkedBlowupSequenceData T.structMap T.ideal T.mult T.boundary hmk).toMarkedSequenceOfBlowups.schemeAt t)
      (MarkedSequenceOfBlowups.projectionToSpec
        (d.toMarkedBlowupSequenceData T.structMap T.ideal T.mult T.boundary hmk).toMarkedSequenceOfBlowups t)
      ((d.toMarkedBlowupSequenceData T.structMap T.ideal T.mult T.boundary hmk).toMarkedSequenceOfBlowups.ideal t)
      T.mult
      (MarkedSequenceOfBlowups.boundaryLocus
        (d.toMarkedBlowupSequenceData T.structMap T.ideal T.mult T.boundary hmk).toMarkedSequenceOfBlowups t)
      ((d.toMarkedBlowupSequenceData T.structMap T.ideal T.mult T.boundary hmk).toMarkedSequenceOfBlowups.center t) := by
  classical
  have hflat := hd.flat_coverMap T h
  have hsurjc := hd.surjective_coverMap T h
  have htun : MaxContactCoverData.balancedTunedIdeal T h.valid = T.ideal :=
    hd.tunedIdeal_of_mult_one T h.valid hone
  have hmul : MaxContactCoverData.tunedMult T = T.mult := by
    show tuningExponent T.mult = T.mult
    rw [hone]
    exact tuningExponent_one
  have hstrictPullback : StrictPullbackBlowupSeq (MaxContactCoverData.coverMap T h.valid)
      (MaxContactCoverData.coverMarkedBlowupData T h.valid hinv (lowerDimensionalFamily A T)).toMarkedSequenceOfBlowups.toSequenceOfBlowups
      d.toSequenceOfBlowups := hpb.toStrictPullbackBlowupSeq
  have hlen : (MaxContactCoverData.coverMarkedBlowupData T h.valid hinv (lowerDimensionalFamily A T)).length = d.length :=
    MarkedBlowupSequenceData.length_eq_of_strictPullbackBlowupSeq _ hstrictPullback
  have htu : t ≤ (MaxContactCoverData.coverMarkedBlowupData T h.valid hinv (lowerDimensionalFamily A T)).length := by omega
  have htlt : t < (MaxContactCoverData.coverMarkedBlowupData T h.valid hinv (lowerDimensionalFamily A T)).length := by omega
  have hN := hd.locallyNoetherian T h d hpb
  have hdiv : ∀ i < d.length, ∃ B',
      Blowup.exceptionalIdeal (d.map i) (d.center i) ^ (MaxContactCoverData.tunedMult T) * B' =
        (d.controlledTransform (MaxContactCoverData.balancedTunedIdeal T h.valid) (MaxContactCoverData.tunedMult T) i).comap
          (d.map i) := by
    rw [htun, hmul]
    exact hmk.1
  have hid := MarkedBlowupSequenceData.ideal_eq_comap_controlledTransform
    (MaxContactCoverData.coverMarkedBlowupData T h.valid hinv (lowerDimensionalFamily A T)) hstrictPullback hdiv t htu
  have hctr := MarkedBlowupSequenceData.center_eq_comap_strictPullbackComparisonMap
    (MaxContactCoverData.coverMarkedBlowupData T h.valid hinv (lowerDimensionalFamily A T)) hstrictPullback t htlt
  have hbd := boundary_eq_map_comap_strictPullbackComparisonMap_of_flat hflat
    (MaxContactCoverData.coverMarkedBlowupData T h.valid hinv (lowerDimensionalFamily A T)) hstrictPullback hN.1 hN.2 t htu
  have hstr := isPullback_projectionToBase_of_isPullback_blowupMorphism (MaxContactCoverData.coverMap T h.valid)
    (MaxContactCoverData.coverMarkedBlowupData T h.valid hinv (lowerDimensionalFamily A T)).toMarkedSequenceOfBlowups.toSequenceOfBlowups d.toSequenceOfBlowups
    (MaxContactCoverData.coverMarkedBlowupData T h.valid hinv (lowerDimensionalFamily A T)).toMarkedSequenceOfBlowups.toSequenceOfBlowups.length
    (fun i hi => hstrictPullback.comp i hi) hstrictPullback.comp_zero (fun i hi => hstrictPullback.pullback i hi) t
    (MarkedBlowupSequenceData.le_toSequenceOfBlowups_length _ htu)
  have hw : (MaxContactCoverData.coverMarkedBlowupData T h.valid hinv (lowerDimensionalFamily A T)).toMarkedSequenceOfBlowups.projectionToBase t ≫
      MaxContactCoverData.coverMap T h.valid =
      hstrictPullback.comp t (MarkedBlowupSequenceData.le_toSequenceOfBlowups_length _ htu) ≫ d.projectionToBase t := by
    rw [← BlowupSequenceData.toSequenceOfBlowups_projectionToBase]
    exact hstr.w.symm
  have hw' : (MaxContactCoverData.coverMarkedBlowupData T h.valid hinv (lowerDimensionalFamily A T)).toMarkedSequenceOfBlowups.projectionToBase t ≫
      MaxContactCoverData.coverMap T h.valid =
      ((MaxContactCoverData.coverMarkedBlowupData T h.valid hinv (lowerDimensionalFamily A T)).strictPullbackComparisonMap hstrictPullback t htu) ≫
        d.projectionToBase t := hw
  have hcs := MaxContactCoverData.coverTriple_structureMorphism T h.valid
  have e1 : (MaxContactCoverData.coverMarkedBlowupData T h.valid hinv (lowerDimensionalFamily A T)).toMarkedSequenceOfBlowups.projectionToBase t ≫
      (MaxContactCoverData.coverTriple T h.valid).structMap =
      ((MaxContactCoverData.coverMarkedBlowupData T h.valid hinv (lowerDimensionalFamily A T)).strictPullbackComparisonMap hstrictPullback t htu) ≫
        (d.projectionToBase t ≫ T.structMap) :=
    (congrArg (fun φ =>
        (MaxContactCoverData.coverMarkedBlowupData T h.valid hinv (lowerDimensionalFamily A T)).toMarkedSequenceOfBlowups.projectionToBase t ≫ φ)
        hcs).trans
      (((Category.assoc _ _ _).symm).trans
        ((congrArg (fun φ => φ ≫ T.structMap) hw').trans (Category.assoc _ _ _)))
  have hci : d.controlledTransform (MaxContactCoverData.balancedTunedIdeal T h.valid)
      (MaxContactCoverData.coverTriple T h.valid).mult t = d.controlledTransform T.ideal T.mult t := by
    rw [htun, MaxContactCoverData.coverTriple_mult, hmul]
  have e2 : (MaxContactCoverData.coverMarkedBlowupData T h.valid hinv (lowerDimensionalFamily A T)).toMarkedSequenceOfBlowups.ideal t =
      (((d.toMarkedBlowupSequenceData T.structMap T.ideal T.mult T.boundary hmk).toMarkedSequenceOfBlowups.ideal t).comap
        ((MaxContactCoverData.coverMarkedBlowupData T h.valid hinv (lowerDimensionalFamily A T)).strictPullbackComparisonMap hstrictPullback t htu)) := by
    simp only [MarkedBlowupSequenceData.toMarkedSequence_ideal, BlowupSequenceData.toMarkedBlowupSequenceData_ideal]
    exact hid.trans (congrArg (fun J => J.comap
      ((MaxContactCoverData.coverMarkedBlowupData T h.valid hinv (lowerDimensionalFamily A T)).strictPullbackComparisonMap hstrictPullback t htu)) hci)
  have e3 : (MaxContactCoverData.coverMarkedBlowupData T h.valid hinv (lowerDimensionalFamily A T)).toMarkedSequenceOfBlowups.center t =
      (((d.toMarkedBlowupSequenceData T.structMap T.ideal T.mult T.boundary hmk).toMarkedSequenceOfBlowups.center t).comap
        ((MaxContactCoverData.coverMarkedBlowupData T h.valid hinv (lowerDimensionalFamily A T)).strictPullbackComparisonMap hstrictPullback t htu)) := by
    simp only [MarkedBlowupSequenceData.toMarkedSequence_center, BlowupSequenceData.toMarkedBlowupSequenceData_center]
    exact hctr
  have e4 : MarkedSequenceOfBlowups.boundaryLocus
      (MaxContactCoverData.coverMarkedBlowupData T h.valid hinv (lowerDimensionalFamily A T)).toMarkedSequenceOfBlowups t =
      ((MaxContactCoverData.coverMarkedBlowupData T h.valid hinv (lowerDimensionalFamily A T)).strictPullbackComparisonMap hstrictPullback t htu) ⁻¹'
        MarkedSequenceOfBlowups.boundaryLocus
          (d.toMarkedBlowupSequenceData T.structMap T.ideal T.mult T.boundary hmk).toMarkedSequenceOfBlowups t := by
    simp only [boundaryLocus_eq_iUnion_support, MarkedBlowupSequenceData.toMarkedSequence_boundary,
      BlowupSequenceData.toMarkedBlowupSequenceData_boundary]
    rw [hbd]
    exact iUnion_support_comap_eq_preimage _ _
  have hp : MarkedSequenceOfBlowups.projectionToSpec
      (d.toMarkedBlowupSequenceData T.structMap T.ideal T.mult T.boundary hmk).toMarkedSequenceOfBlowups t
      = d.projectionToBase t ≫ T.structMap := by
    simp only [MarkedSequenceOfBlowups.projectionToSpec_eq, MarkedBlowupSequenceData.toMarkedSequence_projectionToBase,
      BlowupSequenceData.toMarkedBlowupSequenceData_projectionToBase]
    rfl
  refine orderCertificate_congr_map hp.symm ?_
  refine hd.cert_descend T.base
      ((MaxContactCoverData.coverMarkedBlowupData T h.valid hinv (lowerDimensionalFamily A T)).obj t) _ _
      ((MaxContactCoverData.coverMarkedBlowupData T h.valid hinv (lowerDimensionalFamily A T)).strictPullbackComparisonMap hstrictPullback t htu) ?_ ?_
      _ _ _ _ ?_
  · exact hd.comp_openImmersion T h d hstrictPullback t htu
  · exact surjective_strictPullbackComparisonMap_of_flat_of_surjective hflat hsurjc
      (MaxContactCoverData.coverMarkedBlowupData T h.valid hinv (lowerDimensionalFamily A T)) hstrictPullback t htu
  · have hc : OrderCertificate
        ((MaxContactCoverData.coverMarkedBlowupData T h.valid hinv (lowerDimensionalFamily A T)).toMarkedSequenceOfBlowups.schemeAt t)
        ((MaxContactCoverData.coverMarkedBlowupData T h.valid hinv (lowerDimensionalFamily A T)).toMarkedSequenceOfBlowups.projectionToBase t ≫
          (MaxContactCoverData.coverTriple T h.valid).structMap)
        ((MaxContactCoverData.coverMarkedBlowupData T h.valid hinv (lowerDimensionalFamily A T)).toMarkedSequenceOfBlowups.ideal t) 1
        (MarkedSequenceOfBlowups.boundaryLocus
          (MaxContactCoverData.coverMarkedBlowupData T h.valid hinv (lowerDimensionalFamily A T)).toMarkedSequenceOfBlowups t)
        ((MaxContactCoverData.coverMarkedBlowupData T h.valid hinv (lowerDimensionalFamily A T)).toMarkedSequenceOfBlowups.center t) :=
      hstar.cert T h hone t htlt
    rw [e1, e2, e3, e4] at hc
    exact orderCertificate_congr_mult hone.symm hc

theorem orderCertificate_of_orderAt_le_mult (hstar : CoverSequenceProperties hinv P A) (hd : DescentHypotheses hinv P A B)
    (T : MarkedIdealWithBoundary.{u}) (hv : T.IsAdmissible) (hdim : P T.krullDimSucc)
    (hord : ∀ x : ↥T.scheme, orderAt T.ideal x ≤ (T.mult : ℕ∞))
    (t : ℕ) (ht : t < (maxContactPrincipalization hinv A T).length) :
    OrderCertificate ((maxContactPrincipalization hinv A T).schemeAt t)
      (MarkedSequenceOfBlowups.projectionToSpec (maxContactPrincipalization hinv A T) t)
      ((maxContactPrincipalization hinv A T).ideal t)
      T.mult
      (MarkedSequenceOfBlowups.boundaryLocus (maxContactPrincipalization hinv A T) t)
      ((maxContactPrincipalization hinv A T).center t) := by
  classical
  rcases Nat.lt_or_ge T.mult 2 with hm2 | hm2
  · have hone : T.mult = 1 := le_antisymm (by omega) hv.one_le_mult
    by_cases hemp : orderAtLeastLocus T.ideal T.mult = ∅
    · have h0 := length_eq_zero_of_orderAtLeastLocus_eq_empty hinv P A T hv hdim hord hemp
      omega
    · have hyp : OrderReductionHypotheses P T := ⟨hdim, hord, Set.nonempty_iff_ne_empty.2 hemp, hv⟩
      obtain ⟨d, hm', hpb', heq⟩ := exists_blowupSequenceData_isStrictPullback_cover hinv P A B hstar hd T hyp
      have honeT : (MaxContactReduction.dropTrivialBoundary T).mult = 1 := by
        rw [MaxContactReduction.dropTrivialBoundary_mult]; exact hone
      have htrim : OrderReductionHypotheses P (MaxContactReduction.dropTrivialBoundary T) := hyp.dropTrivialBoundary hd
      have hmk0 := hd.isMarked (MaxContactReduction.dropTrivialBoundary T) htrim d hpb'
      have htun : MaxContactCoverData.balancedTunedIdeal (MaxContactReduction.dropTrivialBoundary T) htrim.valid =
          (MaxContactReduction.dropTrivialBoundary T).ideal :=
        hd.tunedIdeal_of_mult_one (MaxContactReduction.dropTrivialBoundary T) htrim.valid honeT
      have hmul : MaxContactCoverData.tunedMult (MaxContactReduction.dropTrivialBoundary T)
          = (MaxContactReduction.dropTrivialBoundary T).mult := by
        show tuningExponent (MaxContactReduction.dropTrivialBoundary T).mult = (MaxContactReduction.dropTrivialBoundary T).mult
        rw [honeT]
        exact tuningExponent_one
      rw [htun, hmul] at hmk0
      have htlen : t < d.length := by
        rw [heq] at ht
        rw [MarkedBlowupSequenceData.toMarkedSequence_length, BlowupSequenceData.toMarkedBlowupSequenceData_length] at ht
        exact ht
      have hcert := orderCertificate_of_isStrictPullbackBlowupSeq hinv P A B hstar hd (MaxContactReduction.dropTrivialBoundary T) htrim honeT d
        hmk0 hpb' t htlen
      have hsub : MarkedSequenceOfBlowups.boundaryLocus
          (d.toMarkedBlowupSequenceData (MaxContactReduction.dropTrivialBoundary T).structMap (MaxContactReduction.dropTrivialBoundary T).ideal
            (MaxContactReduction.dropTrivialBoundary T).mult (MaxContactReduction.dropTrivialBoundary T).boundary hmk0).toMarkedSequenceOfBlowups t ⊆
          MarkedSequenceOfBlowups.boundaryLocus
            (d.toMarkedBlowupSequenceData T.structMap T.ideal T.mult T.boundary hm').toMarkedSequenceOfBlowups t := by
        simp only [boundaryLocus_eq_iUnion_support, MarkedBlowupSequenceData.toMarkedSequence_boundary,
          BlowupSequenceData.toMarkedBlowupSequenceData_boundary]
        intro x hx
        obtain ⟨D, hD, hxD⟩ := Set.mem_iUnion₂.1 hx
        exact Set.mem_iUnion₂.2 ⟨D, mem_boundary_of_mem_boundary_dropTrivialBoundary T d t D hD, hxD⟩
      have hfin := orderCertificate_mono_of_subset hsub hcert
      rw [heq]
      exact orderCertificate_congr_mult (MaxContactReduction.dropTrivialBoundary_mult T) hfin
  · exact OrderCertificate.of_two_le _ _ _ _ _ _ hm2

end

end MaxContactFunctoriality

end FunctorialResolution.EmbeddedResolution
