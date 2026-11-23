import Mathlib
import Development.ResolutionOfSingularities.Foundations.Blowup.BlowupProperties
import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.ClopenRestriction
import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.BlowupSequenceRelations
import Development.ResolutionOfSingularities.EmbeddedResolution.StrictTransformCharts.CoordinateBlowupChart
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.CoordinateDivisorSmoothness
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.EtaleChartExistence
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.StrictNormalCrossings
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.SmoothDivisorEtaleChart
import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.DerivativeIdealSheaf
import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.IdealSheafOrder
import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.OrderPullback
import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.DerivativeIdealSheafOrderDecrease
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.PullbackBlowupSequenceComposition
import Development.ResolutionOfSingularities.EmbeddedResolution.MaximalContactHypersurfaces.MaxContactHypersurface
import Development.ResolutionOfSingularities.EmbeddedResolution.MaximalContactHypersurfaces.MaxContactIdeal
import Development.ResolutionOfSingularities.EmbeddedResolution.MaximalContactHypersurfaces.MaxContactCoordinate
import Development.ResolutionOfSingularities.EmbeddedResolution.MaximalContactHypersurfaces.TunedSheaf
import Development.ResolutionOfSingularities.EmbeddedResolution.MaximalContactHypersurfaces.TunedSheafBasic
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReductionProperties
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedOrderReduction.ConcatComparisonMap
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.TunedMarkedBlowupSeq
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.CoverMapSurjective
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.MaxContactGeometryHypotheses
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.IndependenceOfHypersurface
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.MaxContactReduction
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.BoundarySeparation
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.CoverTriple
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.DescentHypotheses
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.DerivedAndCoverTriples
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.EmptyOrderLocusAfterReduction
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.MaxContactCover
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.MaxContactCoverProperties
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReduction.MaxContactHypersurfaceTransform
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.BlowupSequenceData
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.Append
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.ControlledTransform
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.IdealBlowupSequence
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.MarkedSequenceOfBlowups
import Development.ResolutionOfSingularities.EmbeddedResolution.StrongResolution.SequenceIsomorphism
import Development.ResolutionOfSingularities.Foundations.BlowupUniversalProperty
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionOfSingularities
universe u

open CategoryTheory AlgebraicGeometry

namespace FunctorialResolution.EmbeddedResolution

private theorem balancedTunedSheaf_eq_self_of_mult_eq_one (k : Type u) [Field k] [CharZero k] {X : Scheme.{u}}
    (pp : X ⟶ Spec (CommRingCat.of k)) [AlgebraicGeometry.Smooth pp]
    [AlgebraicGeometry.LocallyOfFiniteType pp] (I : X.IdealSheafData) (m : ℕ) (hm : m = 1) :
    balancedTunedSheaf k pp I m = I := by
  subst hm
  exact balancedTunedSheaf_one k pp I

private theorem markedIdealWithBoundary_mk_congr {k : Type u} [Field k] {X : Scheme.{u}}
    {p p' : X ⟶ Spec (CommRingCat.of k)} {I I' : X.IdealSheafData} {m m' : ℕ}
    {E E' : List X.IdealSheafData}
    (hp : p = p') (hI : I = I') (hm : m = m') (hE : E = E') :
    MarkedIdealWithBoundary.mk k X p I m E = MarkedIdealWithBoundary.mk k X p' I' m' E' := by
  subst hp
  subst hI
  subst hm
  subst hE
  rfl

private theorem projectionToBase_emptyMarkedBlowupSequenceData_comp (S : MarkedIdealWithBoundary.{u}) :
    (emptyMarkedBlowupSequenceData S.structMap S.ideal S.mult S.boundary).proj
        (emptyMarkedBlowupSequenceData S.structMap S.ideal S.mult S.boundary).length ≫ S.structMap
      = S.structMap :=
  Category.id_comp S.structMap

private theorem structureMorphism_derivedTriple_emptyMarkedBlowupSequenceData (S : MarkedIdealWithBoundary.{u})
    (hft : AlgebraicGeometry.LocallyOfFiniteType
      ((emptyMarkedBlowupSequenceData S.structMap S.ideal S.mult S.boundary).proj
        (emptyMarkedBlowupSequenceData S.structMap S.ideal S.mult S.boundary).length ≫ S.structMap))
    (extra : List ((emptyMarkedBlowupSequenceData S.structMap S.ideal S.mult S.boundary).obj
      (emptyMarkedBlowupSequenceData S.structMap S.ideal S.mult S.boundary).length).IdealSheafData)
    (keep : ℕ) :
    (MaxContactCoverData.derivedTriple S (emptyMarkedBlowupSequenceData S.structMap S.ideal S.mult S.boundary) hft
      extra keep).structMap = S.structMap := by
  rw [MaxContactCoverData.derivedTriple_structureMorphism]
  exact projectionToBase_emptyMarkedBlowupSequenceData_comp S

private theorem ideal_derivedTriple_emptyMarkedBlowupSequenceData (S : MarkedIdealWithBoundary.{u}) (hcz : CharZero S.base)
    (h1 : S.mult = 1)
    (hft : AlgebraicGeometry.LocallyOfFiniteType
      ((emptyMarkedBlowupSequenceData S.structMap S.ideal S.mult S.boundary).proj
        (emptyMarkedBlowupSequenceData S.structMap S.ideal S.mult S.boundary).length ≫ S.structMap))
    (hsm : AlgebraicGeometry.Smooth
      ((emptyMarkedBlowupSequenceData S.structMap S.ideal S.mult S.boundary).proj
        (emptyMarkedBlowupSequenceData S.structMap S.ideal S.mult S.boundary).length ≫ S.structMap))
    (extra : List ((emptyMarkedBlowupSequenceData S.structMap S.ideal S.mult S.boundary).obj
      (emptyMarkedBlowupSequenceData S.structMap S.ideal S.mult S.boundary).length).IdealSheafData)
    (keep : ℕ) :
    (MaxContactCoverData.derivedTriple S (emptyMarkedBlowupSequenceData S.structMap S.ideal S.mult S.boundary) hft
      extra keep).ideal = S.ideal := by
  have := hcz
  have := hft
  have := hsm
  rw [LowerDimReductionPullback.ideal_derivedTriple]
  exact Eq.trans
    (balancedTunedSheaf_eq_self_of_mult_eq_one S.base
      ((emptyMarkedBlowupSequenceData S.structMap S.ideal S.mult S.boundary).proj
        (emptyMarkedBlowupSequenceData S.structMap S.ideal S.mult S.boundary).length ≫ S.structMap)
      ((emptyMarkedBlowupSequenceData S.structMap S.ideal S.mult S.boundary).ideal
        (emptyMarkedBlowupSequenceData S.structMap S.ideal S.mult S.boundary).length) S.mult h1)
    (emptyMarkedBlowupSequenceData_ideal S.structMap S.ideal S.mult S.boundary
      (emptyMarkedBlowupSequenceData S.structMap S.ideal S.mult S.boundary).length)

private theorem mult_derivedTriple_emptyMarkedBlowupSequenceData (S : MarkedIdealWithBoundary.{u}) (h1 : S.mult = 1)
    (hft : AlgebraicGeometry.LocallyOfFiniteType
      ((emptyMarkedBlowupSequenceData S.structMap S.ideal S.mult S.boundary).proj
        (emptyMarkedBlowupSequenceData S.structMap S.ideal S.mult S.boundary).length ≫ S.structMap))
    (extra : List ((emptyMarkedBlowupSequenceData S.structMap S.ideal S.mult S.boundary).obj
      (emptyMarkedBlowupSequenceData S.structMap S.ideal S.mult S.boundary).length).IdealSheafData)
    (keep : ℕ) :
    (MaxContactCoverData.derivedTriple S (emptyMarkedBlowupSequenceData S.structMap S.ideal S.mult S.boundary) hft
      extra keep).mult = 1 := by
  rw [MaxContactCoverData.derivedTriple_mult, h1]
  exact tuningExponent_one

private theorem boundary_derivedTriple_emptyMarkedBlowupSequenceData (S : MarkedIdealWithBoundary.{u})
    (hft : AlgebraicGeometry.LocallyOfFiniteType
      ((emptyMarkedBlowupSequenceData S.structMap S.ideal S.mult S.boundary).proj
        (emptyMarkedBlowupSequenceData S.structMap S.ideal S.mult S.boundary).length ≫ S.structMap))
    (extra : List ((emptyMarkedBlowupSequenceData S.structMap S.ideal S.mult S.boundary).obj
      (emptyMarkedBlowupSequenceData S.structMap S.ideal S.mult S.boundary).length).IdealSheafData) :
    (MaxContactCoverData.derivedTriple S (emptyMarkedBlowupSequenceData S.structMap S.ideal S.mult S.boundary) hft
      extra S.boundary.length).boundary = extra := by
  have hB : (emptyMarkedBlowupSequenceData S.structMap S.ideal S.mult S.boundary).boundary
      (emptyMarkedBlowupSequenceData S.structMap S.ideal S.mult S.boundary).length = S.boundary :=
    emptyMarkedBlowupSequenceData_boundary S.structMap S.ideal S.mult S.boundary
      (emptyMarkedBlowupSequenceData S.structMap S.ideal S.mult S.boundary).length
  have hdrop : List.drop S.boundary.length
      ((emptyMarkedBlowupSequenceData S.structMap S.ideal S.mult S.boundary).boundary
        (emptyMarkedBlowupSequenceData S.structMap S.ideal S.mult S.boundary).length) = [] := by
    rw [hB]
    simp
  rw [MaxContactCoverData.derivedTriple_boundary, hdrop]
  exact List.append_nil extra

private theorem isomorphic_of_emptyMarkedBlowupSequenceData_append {k : Type u} [Field k] {X : Scheme.{u}}
    (p : X ⟶ Spec (CommRingCat.of k)) (I : X.IdealSheafData) (m : ℕ)
    (E : List X.IdealSheafData)
    (t : MarkedBlowupSequenceData
      ((emptyMarkedBlowupSequenceData p I m E).proj (emptyMarkedBlowupSequenceData p I m E).toBlowupSequenceData.length ≫ p)
      ((emptyMarkedBlowupSequenceData p I m E).ideal (emptyMarkedBlowupSequenceData p I m E).toBlowupSequenceData.length) m
      ((emptyMarkedBlowupSequenceData p I m E).boundary (emptyMarkedBlowupSequenceData p I m E).toBlowupSequenceData.length))
    (hinv : ComapIsoInvariance.{u}) :
    ((emptyMarkedBlowupSequenceData p I m E).append t hinv).toSequenceOfBlowups.Isomorphic t.toSequenceOfBlowups := by
  have hmain := MarkedBlowupSequenceData.emptyMarkedBlowupSequenceData_append_isomorphic p I m E t hinv
  have e1 := MarkedBlowupSequenceData.toMarkedSequence_toSequenceOfBlowups ((emptyMarkedBlowupSequenceData p I m E).append t hinv)
  have e2 := MarkedBlowupSequenceData.toMarkedSequence_toSequenceOfBlowups t
  rw [e1, e2] at hmain
  exact hmain

private theorem derivIdealSheaf_eq_top_of_orderAt_le_one (k : Type u) [Field k] [CharZero k]
    {P : Scheme.{u}} (p : P ⟶ Spec (CommRingCat.of k)) [AlgebraicGeometry.Smooth p]
    [AlgebraicGeometry.LocallyOfFiniteType p] (A : P.IdealSheafData)
    (hord : ∀ x : ↥P, orderAt A x ≤ ((1 : ℕ) : ℕ∞)) :
    derivIdealSheaf k p A = ⊤ := by
  have hempty : orderAtLeastLocus A 2 = ∅ := by
    ext x
    simp only [Set.mem_empty_iff_false, iff_false]
    intro hx
    have h2 : ((2 : ℕ) : ℕ∞) ≤ orderAt A x := (mem_orderAtLeastLocus_iff A 2 x).1 hx
    have h21 : ((2 : ℕ) : ℕ∞) ≤ ((1 : ℕ) : ℕ∞) := le_trans h2 (hord x)
    have h21' : (2 : ℕ) ≤ 1 := by exact_mod_cast h21
    omega
  have h := orderAtLeastLocus_derivIdealSheafIterate k p A (r := 1) (m := 2) (by norm_num)
  rw [hempty] at h
  have h1 : orderAtLeastLocus (derivIdealSheafIterate k p 1 A) 1 = ∅ := h
  have hiter : derivIdealSheaf k p A = derivIdealSheafIterate k p 1 A := rfl
  rw [hiter]
  refine (AlgebraicGeometry.Scheme.IdealSheafData.eq_top_iff_support_eq_empty _).2 ?_
  ext y
  simp only [Set.mem_empty_iff_false, iff_false]
  intro hy
  have hy1 : y ∈ orderAtLeastLocus (derivIdealSheafIterate k p 1 A) 1 :=
    (mem_orderAtLeastLocus_one_iff _ y).2 hy
  rw [h1] at hy1
  exact hy1

private theorem isMaxContactInvariant_of_mult_eq_one (k : Type u) [Field k] [CharZero k]
    {P : Scheme.{u}} (p : P ⟶ Spec (CommRingCat.of k)) [AlgebraicGeometry.Smooth p]
    [AlgebraicGeometry.LocallyOfFiniteType p] (A : P.IdealSheafData) (m : ℕ) (hm : m = 1)
    (hord : ∀ x : ↥P, orderAt A x ≤ ((1 : ℕ) : ℕ∞)) :
    IsMaxContactInvariant k p A m := by
  subst hm
  unfold FunctorialResolution.EmbeddedResolution.IsMaxContactInvariant
  rw [derivIdealSheaf_eq_top_of_orderAt_le_one k p A hord]
  have hmc : maxContactIdeal k p A 1 = A := rfl
  rw [hmc]
  simp

private theorem coordIdeal_comp_map_eq_comap {X Y : Scheme.{u}} {k : Type u} [Field k]
    {p : X ⟶ Spec (CommRingCat.of k)} {q : Y ⟶ Spec (CommRingCat.of k)}
    {U : X.Opens} {V : Y.Opens} {n : ℕ} (c : EtaleChart p U n)
    (φ : (V : Scheme.{u}) ⟶ (U : Scheme.{u}))
    (hcs : (φ ≫ c.map) ≫ affineSpaceFinToSpec k n = V.ι ≫ q)
    (he : AlgebraicGeometry.Etale (φ ≫ c.map)) (S : Finset (Fin n)) :
    (⟨φ ≫ c.map, hcs, he⟩ : EtaleChart q V n).coordIdeal S = (c.coordIdeal S).comap φ := by
  rw [EtaleChart.coordIdeal_eq_comap_coordSubspaceIdeal, EtaleChart.coordIdeal_eq_comap_coordSubspaceIdeal]
  show (coordSubspaceIdeal k n S).comap (φ ≫ c.map)
      = ((coordSubspaceIdeal k n S).comap c.map).comap φ
  rw [Scheme.IdealSheafData.comap_comp]

theorem isMaxContactHypersurface_one_of_etaleChart {k : Type u} [Field k] [CharZero k]
    {P : Scheme.{u}} (p : P ⟶ Spec (CommRingCat.of k)) [AlgebraicGeometry.Smooth p]
    [AlgebraicGeometry.LocallyOfFiniteType p] (A D : P.IdealSheafData)
    (hchart : ∀ x : ↥P, x ∈ D.support →
      ∃ (U : P.Opens) (n : ℕ) (c : EtaleChart p U n) (j : Fin n),
        x ∈ U ∧ restrictIdeal D U = c.coordIdeal ({j} : Finset (Fin n)))
    (hDle : D ≤ A) :
    IsMaxContactHypersurface k p A 1 D := by
  intro x
  by_cases hx : x ∈ D.support
  · obtain ⟨U, n, c, j, hxU, hcoord⟩ := hchart x hx
    obtain ⟨V, hVaff, hxV, hVU⟩ :
        ∃ V : P.Opens, AlgebraicGeometry.IsAffineOpen V ∧ x ∈ V ∧ V ≤ U :=
      exists_isAffineOpen_mem_and_subset hxU
    refine ⟨V, hVaff, hxV, Or.inr ⟨n, c.restrict hVU, j, ?_, ?_⟩⟩
    · exact restrictIdeal_eq_restrict_coordIdeal_of_le hVU c D ({j} : Finset (Fin n)) hcoord
    · rw [isMaxContactCoord_one_iff,
        ← restrictIdeal_eq_restrict_coordIdeal_of_le hVU c D ({j} : Finset (Fin n)) hcoord,
        restrictIdeal_eq_comap_ι, restrictIdeal_eq_comap_ι]
      exact Scheme.IdealSheafData.comap_mono _ hDle
  · have hclosed : IsClosed ((D.support : Set ↥P)) := D.support.isClosed
    obtain ⟨V, hVaff, hxV, hVW⟩ :
        ∃ V : P.Opens, AlgebraicGeometry.IsAffineOpen V ∧ x ∈ V ∧
          V ≤ (⟨((D.support : Set ↥P))ᶜ, hclosed.isOpen_compl⟩ : P.Opens) :=
      exists_isAffineOpen_mem_and_subset hx
    have hdisj : Disjoint ((D.support : Set ↥P)) ((V : Set ↥P)) := by
      rw [Set.disjoint_right]
      intro y hyV hyD
      exact (hVW hyV) hyD
    have htop : restrictIdeal D V = ⊤ :=
      (FunctorialResolution.EmbeddedResolution.restrictIdeal_eq_top_iff_forall_notMem_support _ _).mpr
        (fun y hyV hyD => Set.disjoint_left.mp hdisj hyD hyV)
    refine ⟨V, hVaff, hxV, Or.inl ⟨?_, htop⟩⟩
    rw [Set.disjoint_left]
    intro y hy hyV
    have h1 : y ∈ D.support :=
      (one_le_orderAt_iff_mem_support D y).1
        (le_trans ((one_le_orderAt_iff_mem_support A y).2 ((mem_orderAtLeastLocus_one_iff A y).1 hy))
          (orderAt_le_of_le hDle y))
    exact (Set.disjoint_left.mp hdisj h1) hyV

theorem IsMaxContactHypersurface.comap_of_isOpenImmersionAtSource {k : Type u} [Field k] [CharZero k]
    {P P' : Scheme.{u}} (p : P ⟶ Spec (CommRingCat.of k)) [AlgebraicGeometry.Smooth p]
    [AlgebraicGeometry.LocallyOfFiniteType p] {A H : P.IdealSheafData}
    (hH : IsMaxContactHypersurface k p A 1 H) (g : P' ⟶ P) [AlgebraicGeometry.Smooth g]
    [AlgebraicGeometry.LocallyOfFiniteType (g ≫ p)]
    (hg : MaxContactFunctoriality.IsLocalIsomorphism g) :
    IsMaxContactHypersurface k (g ≫ p) (A.comap g) 1 (H.comap g) := by
  have : AlgebraicGeometry.Smooth (g ≫ p) := inferInstance
  intro x'
  obtain ⟨U₀, hxU₀, hoi⟩ := hg x'
  have := hoi
  obtain ⟨U, _, hxU, hcase⟩ := hH (g.base x')
  have hxpre : x' ∈ (g ⁻¹ᵁ U) := hxU
  obtain ⟨V, hVaff, hxV, hVW⟩ :
      ∃ V : P'.Opens, AlgebraicGeometry.IsAffineOpen V ∧ x' ∈ V ∧ V ≤ U₀ ⊓ (g ⁻¹ᵁ U) :=
    exists_isAffineOpen_mem_and_subset (⟨hxU₀, hxpre⟩ : x' ∈ U₀ ⊓ (g ⁻¹ᵁ U))
  have hVU₀ : V ≤ U₀ := le_trans hVW inf_le_left
  have hVpre : V ≤ (g ⁻¹ᵁ U) := le_trans hVW inf_le_right
  obtain ⟨φ, hφ⟩ : ∃ φ, φ = P'.homOfLE hVpre ≫ (g ∣_ U) := ⟨_, rfl⟩
  have hfac : V.ι ≫ g = φ ≫ U.ι := by
    rw [hφ, Category.assoc, morphismRestrict_ι, ← Category.assoc, P'.homOfLE_ι]
  have hoiV : AlgebraicGeometry.IsOpenImmersion (V.ι ≫ g) := by
    have hrw : V.ι ≫ g = P'.homOfLE hVU₀ ≫ (U₀.ι ≫ g) := by
      rw [← Category.assoc, P'.homOfLE_ι]
    rw [hrw]
    infer_instance
  have : AlgebraicGeometry.IsOpenImmersion (φ ≫ U.ι) := by
    rw [← hfac]
    exact hoiV
  have : AlgebraicGeometry.IsOpenImmersion φ :=
    AlgebraicGeometry.IsOpenImmersion.of_comp φ U.ι
  have : AlgebraicGeometry.Etale φ := inferInstance
  have hcomapres : ∀ J : P.IdealSheafData,
      restrictIdeal (J.comap g) V = (restrictIdeal J U).comap φ := by
    intro J
    rw [restrictIdeal_eq_comap_ι, restrictIdeal_eq_comap_ι, ← Scheme.IdealSheafData.comap_comp,
      ← Scheme.IdealSheafData.comap_comp, hfac]
  refine ⟨V, hVaff, hxV, ?_⟩
  rcases hcase with ⟨hdisj, htop⟩ | ⟨n, c, j, hcoord, hmc⟩
  · refine Or.inl ⟨?_, ?_⟩
    · rw [orderAtLeastLocus_comap k p g A 1, Set.disjoint_left]
      intro y hy hyV
      exact (Set.disjoint_left.mp hdisj hy) (hVpre hyV)
    · rw [hcomapres H, htop]
      simp
  · have := c.isEtale
    have hcs : (φ ≫ c.map) ≫ affineSpaceFinToSpec k n = V.ι ≫ (g ≫ p) := by
      rw [Category.assoc, c.comp_struct, ← Category.assoc, ← hfac, Category.assoc]
    have he : AlgebraicGeometry.Etale (φ ≫ c.map) := inferInstance
    refine Or.inr ⟨n, ⟨φ ≫ c.map, hcs, he⟩, j, ?_, ?_⟩
    · rw [hcomapres H, hcoord, coordIdeal_comp_map_eq_comap c φ hcs he]
    · rw [isMaxContactCoord_one_iff, coordIdeal_comp_map_eq_comap c φ hcs he, hcomapres A]
      exact Scheme.IdealSheafData.comap_mono _ ((isMaxContactCoord_one_iff k p A c j).1 hmc)

private theorem isBalanced_of_eq_derivedTriple_emptyMarkedBlowupSequenceData (hstar : MaxContactCoverProperties.{u})
    (S : MarkedIdealWithBoundary.{u}) (hSV : S.IsAdmissible)
    (hord : ∀ x : ↥S.scheme, orderAt S.ideal x ≤ ((S.mult : ℕ) : ℕ∞))
    (hft : AlgebraicGeometry.LocallyOfFiniteType
      ((emptyMarkedBlowupSequenceData S.structMap S.ideal S.mult S.boundary).proj
        (emptyMarkedBlowupSequenceData S.structMap S.ideal S.mult S.boundary).length ≫ S.structMap))
    (L : List ((emptyMarkedBlowupSequenceData S.structMap S.ideal S.mult S.boundary).obj
      (emptyMarkedBlowupSequenceData S.structMap S.ideal S.mult S.boundary).length).IdealSheafData)
    (keep : ℕ) (D : MarkedIdealWithBoundary.{u})
    (hDeq : MaxContactCoverData.derivedTriple S
      (emptyMarkedBlowupSequenceData S.structMap S.ideal S.mult S.boundary) hft L keep = D)
    (hVD : D.IsAdmissible) :
    ∀ hft2 : AlgebraicGeometry.LocallyOfFiniteType D.structMap, D.IsBalanced hft2 := by
  subst hDeq
  intro hft2
  exact LowerDimReductionPullback.isBalanced_derivedTriple hstar S hSV hSV.one_le_mult hord
    (emptyMarkedBlowupSequenceData S.structMap S.ideal S.mult S.boundary) hft L keep hVD

private theorem isomorphic_of_isMaxContactHypersurface_singleton_boundary (hin : OrderReduction.OrderReductionHypotheses.{u})
    (P : ℕ → Prop) (hmono : ∀ a b : ℕ, a ≤ b → P b → P a) (A0 B : PrincipalizationAssignment.{u})
    (hspec0 : IsBoundaryDivisorReduction P 0 A0 B) (S : MarkedIdealWithBoundary.{u})
    [CharZero S.base] [AlgebraicGeometry.Smooth S.structMap]
    [AlgebraicGeometry.LocallyOfFiniteType S.structMap]
    (hSV : S.IsAdmissible) (hP : P S.krullDimSucc)
    (hord : ∀ x : ↥S.scheme, orderAt S.ideal x ≤ ((S.mult : ℕ) : ℕ∞))
    (hm1 : S.mult = 1) (H₁ H₂ : S.scheme.IdealSheafData) (hbd : S.boundary = [H₁])
    (hD : ∀ hft2 : AlgebraicGeometry.LocallyOfFiniteType S.structMap, S.IsBalanced hft2)
    (hV₂ : (S.withBoundary [H₂]).IsAdmissible)
    (hH₁ : IsMaxContactHypersurface S.base S.structMap S.ideal S.mult H₁)
    (hH₂ : IsMaxContactHypersurface S.base S.structMap S.ideal S.mult H₂) :
    (A0 S).toSequenceOfBlowups.Isomorphic (A0 (S.withBoundary [H₂])).toSequenceOfBlowups := by
  have hMC : ∀ [AlgebraicGeometry.LocallyOfFiniteType S.structMap],
      IsMaxContactInvariant S.base S.structMap S.ideal S.mult := by
    intro _i
    refine isMaxContactInvariant_of_mult_eq_one S.base S.structMap S.ideal S.mult hm1 ?_
    intro x
    have hx := hord x
    rw [hm1] at hx
    exact hx
  exact DivisorReductionIndependence.isomorphic_withBoundary_cons_of_isMaxContactHypersurface hin P hmono A0 B hspec0 S hSV hP hord hD hMC
    [] H₁ H₂ hbd hV₂ (by intro _i; exact hH₁) (by intro _i; exact hH₂)

namespace MaxContactCoverData

private theorem isStrictPullbackBlowupSeq_cover_of_eq_append (hstar : MaxContactCoverProperties.{u})
    (hin : OrderReduction.OrderReductionHypotheses.{u})
    (hinv : ComapIsoInvariance.{u}) (P : ℕ → Prop) (hmono : ∀ a b : ℕ, a ≤ b → P b → P a)
    (A : ℕ → PrincipalizationAssignment.{u}) (B : PrincipalizationAssignment.{u})
    (hspec : ∀ j : ℕ, IsBoundaryDivisorReduction P j (A j) B)
    (T : MarkedIdealWithBoundary.{u}) (h : MaxContactFunctoriality.OrderReductionHypotheses P T)
    (hbd : T.boundary = []) (hmult : T.mult = 1)
    {Y : Scheme.{u}} (e : Y ⟶ T.scheme) [AlgebraicGeometry.IsClosedImmersion e]
    (hadm : ∀ [AlgebraicGeometry.LocallyOfFiniteType T.structMap],
      IsMaxContactHypersurface T.base T.structMap T.ideal T.mult
        (AlgebraicGeometry.Scheme.Hom.ker e))
    (hV : (T.withBoundary [AlgebraicGeometry.Scheme.Hom.ker e]).IsAdmissible)
    (s : MarkedBlowupSequenceData (coverTriple T h.valid).structMap (coverTriple T h.valid).ideal
      (coverTriple T h.valid).mult (coverTriple T h.valid).boundary)
    (hs : s = emptyMarkedBlowupSequenceData (coverTriple T h.valid).structMap (coverTriple T h.valid).ideal
      (coverTriple T h.valid).mult (coverTriple T h.valid).boundary)
    (hft : AlgebraicGeometry.LocallyOfFiniteType
      (s.proj s.length ≫ (coverTriple T h.valid).structMap))
    (hVc : (derivedTriple (coverTriple T h.valid) s hft
      [MaxContactReduction.strictTransformAtLength s (coverMaxContactIdeal T h.valid)]
      (coverTriple T h.valid).boundary.length).IsAdmissible)
    (hmk : (BlowupSequenceData.ofSequenceOfBlowups (A 0 (derivedTriple (coverTriple T h.valid) s hft
        [MaxContactReduction.strictTransformAtLength s (coverMaxContactIdeal T h.valid)]
        (coverTriple T h.valid).boundary.length)).toSequenceOfBlowups).IsMarked
      (s.proj s.length ≫ (coverTriple T h.valid).structMap) (s.ideal s.length)
      (coverTriple T h.valid).mult (s.boundary s.length))
    (heq : coverMarkedBlowupData T h.valid hinv (MaxContactFunctoriality.lowerDimensionalFamily A T)
      = s.append ((BlowupSequenceData.ofSequenceOfBlowups (A 0 (derivedTriple (coverTriple T h.valid) s hft
          [MaxContactReduction.strictTransformAtLength s (coverMaxContactIdeal T h.valid)]
          (coverTriple T h.valid).boundary.length)).toSequenceOfBlowups).toMarkedBlowupSequenceData
        (s.proj s.length ≫ (coverTriple T h.valid).structMap) (s.ideal s.length)
        (coverTriple T h.valid).mult (s.boundary s.length) hmk) hinv) :
    IsStrictPullbackBlowupSeq (coverMap T h.valid)
      (coverMarkedBlowupData T h.valid hinv (MaxContactFunctoriality.lowerDimensionalFamily A T)).toSequenceOfBlowups
      (A 0 (T.withBoundary [AlgebraicGeometry.Scheme.Hom.ker e])).toSequenceOfBlowups := by
  have := h.valid.locallyOfFiniteType
  have := h.valid.smooth
  have : CharZero T.base := h.valid.charZero
  subst hs
  have := hft
  have hVcover : (coverTriple T h.valid).IsAdmissible :=
    BoundarySeparationByMaxContact.isAdmissible_coverTriple hstar P T h
  have hftC : AlgebraicGeometry.LocallyOfFiniteType (coverTriple T h.valid).structMap :=
    hVcover.locallyOfFiniteType
  have hsmC : AlgebraicGeometry.Smooth (coverTriple T h.valid).structMap := hVcover.smooth
  have hczC : CharZero (coverTriple T h.valid).base := hVcover.charZero
  have hczPB : CharZero
      ((T.withBoundary [AlgebraicGeometry.Scheme.Hom.ker e]).pullbackAlong
        (coverTriple T h.valid).scheme (coverTriple T h.valid).structMap
        (coverMap T h.valid)).base := h.valid.charZero
  have hsmPB : AlgebraicGeometry.Smooth
      ((T.withBoundary [AlgebraicGeometry.Scheme.Hom.ker e]).pullbackAlong
        (coverTriple T h.valid).scheme (coverTriple T h.valid).structMap
        (coverMap T h.valid)).structMap := hVcover.smooth
  have hftPB : AlgebraicGeometry.LocallyOfFiniteType
      ((T.withBoundary [AlgebraicGeometry.Scheme.Hom.ker e]).pullbackAlong
        (coverTriple T h.valid).scheme (coverTriple T h.valid).structMap
        (coverMap T h.valid)).structMap := hVcover.locallyOfFiniteType
  have hOcover := BoundarySeparationByMaxContact.orderAt_coverTriple_ideal_le_mult hstar P T h
  have hsm : AlgebraicGeometry.Smooth
      ((emptyMarkedBlowupSequenceData (coverTriple T h.valid).structMap (coverTriple T h.valid).ideal
          (coverTriple T h.valid).mult (coverTriple T h.valid).boundary).proj
        (emptyMarkedBlowupSequenceData (coverTriple T h.valid).structMap (coverTriple T h.valid).ideal
          (coverTriple T h.valid).mult (coverTriple T h.valid).boundary).length ≫
        (coverTriple T h.valid).structMap) :=
    BoundarySeparationByMaxContact.smooth_projectionToBase_comp hstar (coverTriple T h.valid) hVcover
      (emptyMarkedBlowupSequenceData (coverTriple T h.valid).structMap (coverTriple T h.valid).ideal
        (coverTriple T h.valid).mult (coverTriple T h.valid).boundary)
      (emptyMarkedBlowupSequenceData (coverTriple T h.valid).structMap (coverTriple T h.valid).ideal
        (coverTriple T h.valid).mult (coverTriple T h.valid).boundary).length le_rfl
  have := hsm
  have htunedIdeal : balancedTunedIdeal T h.valid = T.ideal :=
    balancedTunedSheaf_eq_self_of_mult_eq_one T.base T.structMap T.ideal T.mult hmult
  have hcoverMult : (coverTriple T h.valid).mult = 1 := by
    rw [coverTriple_mult]
    show FunctorialResolution.EmbeddedResolution.tuningExponent T.mult = 1
    rw [hmult]
    exact tuningExponent_one
  have hcoverIdeal : (coverTriple T h.valid).ideal = T.ideal.comap (coverMap T h.valid) := by
    rw [coverTriple_ideal, htunedIdeal]
  have hqc : AlgebraicGeometry.QuasiCompact (coverTriple T h.valid).structMap :=
    hVcover.quasiCompact
  have hsurj : AlgebraicGeometry.Surjective (coverMap T h.valid) :=
    surjective_coverMap T h.valid (hstar.exists_goodCover T h.valid h.orderLE)
  have hftE : AlgebraicGeometry.LocallyOfFiniteType
      ((emptyMarkedBlowupSequenceData T.structMap T.ideal T.mult T.boundary).proj
        (emptyMarkedBlowupSequenceData T.structMap T.ideal T.mult T.boundary).length ≫ T.structMap) := by
    have hx : AlgebraicGeometry.LocallyOfFiniteType T.structMap :=
      h.valid.locallyOfFiniteType
    rw [projectionToBase_emptyMarkedBlowupSequenceData_comp T]
    exact hx
  have hsmE : AlgebraicGeometry.Smooth
      ((emptyMarkedBlowupSequenceData T.structMap T.ideal T.mult T.boundary).proj
        (emptyMarkedBlowupSequenceData T.structMap T.ideal T.mult T.boundary).length ≫ T.structMap) := by
    have hx : AlgebraicGeometry.Smooth T.structMap := h.valid.smooth
    rw [projectionToBase_emptyMarkedBlowupSequenceData_comp T]
    exact hx
  have hdrop0 : List.drop 0
      ((emptyMarkedBlowupSequenceData T.structMap T.ideal T.mult T.boundary).boundary
        (emptyMarkedBlowupSequenceData T.structMap T.ideal T.mult T.boundary).length) = [] :=
    (congrArg (List.drop 0)
        (emptyMarkedBlowupSequenceData_boundary T.structMap T.ideal T.mult T.boundary
          (emptyMarkedBlowupSequenceData T.structMap T.ideal T.mult T.boundary).length)).trans
      ((congrArg (List.drop 0) hbd).trans rfl)
  have hbdE : (derivedTriple T (emptyMarkedBlowupSequenceData T.structMap T.ideal T.mult T.boundary) hftE
      [AlgebraicGeometry.Scheme.Hom.ker e] 0).boundary
      = [AlgebraicGeometry.Scheme.Hom.ker e] := by
    rw [derivedTriple_boundary, hdrop0]
    exact List.append_nil [AlgebraicGeometry.Scheme.Hom.ker e]
  have hEqT : derivedTriple T (emptyMarkedBlowupSequenceData T.structMap T.ideal T.mult T.boundary) hftE
      [AlgebraicGeometry.Scheme.Hom.ker e] 0
      = T.withBoundary [AlgebraicGeometry.Scheme.Hom.ker e] :=
    markedIdealWithBoundary_mk_congr
      (structureMorphism_derivedTriple_emptyMarkedBlowupSequenceData T hftE [AlgebraicGeometry.Scheme.Hom.ker e] 0)
      (ideal_derivedTriple_emptyMarkedBlowupSequenceData T h.valid.charZero hmult hftE hsmE
        [AlgebraicGeometry.Scheme.Hom.ker e] 0)
      ((mult_derivedTriple_emptyMarkedBlowupSequenceData T hmult hftE
        [AlgebraicGeometry.Scheme.Hom.ker e] 0).trans hmult.symm)
      hbdE
  have hbalanced := isBalanced_of_eq_derivedTriple_emptyMarkedBlowupSequenceData hstar T h.valid h.orderLE hftE
    [AlgebraicGeometry.Scheme.Hom.ker e] 0
    (T.withBoundary [AlgebraicGeometry.Scheme.Hom.ker e]) hEqT hV
  have hpb := DivisorReductionIndependence.isAdmissible_and_isStrictPullbackBlowupSeq_of_etale hin P hmono (A 0) B (hspec 0)
    (T.withBoundary [AlgebraicGeometry.Scheme.Hom.ker e]) hV h.dim_prop h.orderLE hbalanced
    (Nat.succ_pos 0) (coverTriple T h.valid).scheme (coverTriple T h.valid).structMap
    (coverMap T h.valid) (etale_coverMap_of_isAdmissible T h.valid) hqc
    (coverTriple_structureMorphism T h.valid).symm (fun x _ => hsurj.1 x)
  have hbdU : (derivedTriple (coverTriple T h.valid)
      (emptyMarkedBlowupSequenceData (coverTriple T h.valid).structMap (coverTriple T h.valid).ideal
        (coverTriple T h.valid).mult (coverTriple T h.valid).boundary) hft
      [(AlgebraicGeometry.Scheme.Hom.ker e).comap (coverMap T h.valid)]
      (coverTriple T h.valid).boundary.length).boundary
      = [(AlgebraicGeometry.Scheme.Hom.ker e).comap (coverMap T h.valid)] :=
    boundary_derivedTriple_emptyMarkedBlowupSequenceData (coverTriple T h.valid) hft
      [(AlgebraicGeometry.Scheme.Hom.ker e).comap (coverMap T h.valid)]
  have hEqU : derivedTriple (coverTriple T h.valid)
      (emptyMarkedBlowupSequenceData (coverTriple T h.valid).structMap (coverTriple T h.valid).ideal
        (coverTriple T h.valid).mult (coverTriple T h.valid).boundary) hft
      [(AlgebraicGeometry.Scheme.Hom.ker e).comap (coverMap T h.valid)]
      (coverTriple T h.valid).boundary.length
      = (T.withBoundary [AlgebraicGeometry.Scheme.Hom.ker e]).pullbackAlong
          (coverTriple T h.valid).scheme (coverTriple T h.valid).structMap
          (coverMap T h.valid) :=
    markedIdealWithBoundary_mk_congr
      (structureMorphism_derivedTriple_emptyMarkedBlowupSequenceData (coverTriple T h.valid) hft
        [(AlgebraicGeometry.Scheme.Hom.ker e).comap (coverMap T h.valid)]
        (coverTriple T h.valid).boundary.length)
      ((ideal_derivedTriple_emptyMarkedBlowupSequenceData (coverTriple T h.valid) hczC hcoverMult hft hsm
        [(AlgebraicGeometry.Scheme.Hom.ker e).comap (coverMap T h.valid)]
        (coverTriple T h.valid).boundary.length).trans hcoverIdeal)
      ((mult_derivedTriple_emptyMarkedBlowupSequenceData (coverTriple T h.valid) hcoverMult hft
        [(AlgebraicGeometry.Scheme.Hom.ker e).comap (coverMap T h.valid)]
        (coverTriple T h.valid).boundary.length).trans hmult.symm)
      hbdU
  have hDU := isBalanced_of_eq_derivedTriple_emptyMarkedBlowupSequenceData hstar (coverTriple T h.valid) hVcover
    hOcover hft
    [(AlgebraicGeometry.Scheme.Hom.ker e).comap (coverMap T h.valid)]
    (coverTriple T h.valid).boundary.length
    ((T.withBoundary [AlgebraicGeometry.Scheme.Hom.ker e]).pullbackAlong
      (coverTriple T h.valid).scheme (coverTriple T h.valid).structMap
      (coverMap T h.valid)) hEqU hpb.1
  have hbdU2 : (derivedTriple (coverTriple T h.valid)
      (emptyMarkedBlowupSequenceData (coverTriple T h.valid).structMap (coverTriple T h.valid).ideal
        (coverTriple T h.valid).mult (coverTriple T h.valid).boundary) hft
      [MaxContactReduction.strictTransformAtLength
        (emptyMarkedBlowupSequenceData (coverTriple T h.valid).structMap (coverTriple T h.valid).ideal
          (coverTriple T h.valid).mult (coverTriple T h.valid).boundary)
        (coverMaxContactIdeal T h.valid)]
      (coverTriple T h.valid).boundary.length).boundary
      = [MaxContactReduction.strictTransformAtLength
        (emptyMarkedBlowupSequenceData (coverTriple T h.valid).structMap (coverTriple T h.valid).ideal
          (coverTriple T h.valid).mult (coverTriple T h.valid).boundary)
        (coverMaxContactIdeal T h.valid)] :=
    boundary_derivedTriple_emptyMarkedBlowupSequenceData (coverTriple T h.valid) hft
      [MaxContactReduction.strictTransformAtLength
        (emptyMarkedBlowupSequenceData (coverTriple T h.valid).structMap (coverTriple T h.valid).ideal
          (coverTriple T h.valid).mult (coverTriple T h.valid).boundary)
        (coverMaxContactIdeal T h.valid)]
  have htri : derivedTriple (coverTriple T h.valid)
      (emptyMarkedBlowupSequenceData (coverTriple T h.valid).structMap (coverTriple T h.valid).ideal
        (coverTriple T h.valid).mult (coverTriple T h.valid).boundary) hft
      [MaxContactReduction.strictTransformAtLength
        (emptyMarkedBlowupSequenceData (coverTriple T h.valid).structMap (coverTriple T h.valid).ideal
          (coverTriple T h.valid).mult (coverTriple T h.valid).boundary)
        (coverMaxContactIdeal T h.valid)]
      (coverTriple T h.valid).boundary.length
      = ((T.withBoundary [AlgebraicGeometry.Scheme.Hom.ker e]).pullbackAlong
          (coverTriple T h.valid).scheme (coverTriple T h.valid).structMap
          (coverMap T h.valid)).withBoundary
        [MaxContactReduction.strictTransformAtLength
          (emptyMarkedBlowupSequenceData (coverTriple T h.valid).structMap (coverTriple T h.valid).ideal
            (coverTriple T h.valid).mult (coverTriple T h.valid).boundary)
          (coverMaxContactIdeal T h.valid)] :=
    markedIdealWithBoundary_mk_congr
      (structureMorphism_derivedTriple_emptyMarkedBlowupSequenceData (coverTriple T h.valid) hft
        [MaxContactReduction.strictTransformAtLength
          (emptyMarkedBlowupSequenceData (coverTriple T h.valid).structMap (coverTriple T h.valid).ideal
            (coverTriple T h.valid).mult (coverTriple T h.valid).boundary)
          (coverMaxContactIdeal T h.valid)]
        (coverTriple T h.valid).boundary.length)
      ((ideal_derivedTriple_emptyMarkedBlowupSequenceData (coverTriple T h.valid) hczC hcoverMult hft hsm
        [MaxContactReduction.strictTransformAtLength
          (emptyMarkedBlowupSequenceData (coverTriple T h.valid).structMap (coverTriple T h.valid).ideal
            (coverTriple T h.valid).mult (coverTriple T h.valid).boundary)
          (coverMaxContactIdeal T h.valid)]
        (coverTriple T h.valid).boundary.length).trans hcoverIdeal)
      ((mult_derivedTriple_emptyMarkedBlowupSequenceData (coverTriple T h.valid) hcoverMult hft
        [MaxContactReduction.strictTransformAtLength
          (emptyMarkedBlowupSequenceData (coverTriple T h.valid).structMap (coverTriple T h.valid).ideal
            (coverTriple T h.valid).mult (coverTriple T h.valid).boundary)
          (coverMaxContactIdeal T h.valid)]
        (coverTriple T h.valid).boundary.length).trans hmult.symm)
      hbdU2
  have hV₂ : ((((T.withBoundary [AlgebraicGeometry.Scheme.Hom.ker e]).pullbackAlong
        (coverTriple T h.valid).scheme (coverTriple T h.valid).structMap
        (coverMap T h.valid)).withBoundary
      [MaxContactReduction.strictTransformAtLength
        (emptyMarkedBlowupSequenceData (coverTriple T h.valid).structMap (coverTriple T h.valid).ideal
          (coverTriple T h.valid).mult (coverTriple T h.valid).boundary)
        (coverMaxContactIdeal T h.valid)])).IsAdmissible := by
    rw [← htri]
    exact hVc
  have hcmp : AlgebraicGeometry.LocallyOfFiniteType (coverMap T h.valid ≫ T.structMap) := by
    rw [← coverTriple_structureMorphism T h.valid]
    exact hftC
  have hadm1 : IsMaxContactHypersurface T.base T.structMap T.ideal 1
      (AlgebraicGeometry.Scheme.Hom.ker e) := by
    have hx := hadm
    rw [hmult] at hx
    exact hx
  have hkey := IsMaxContactHypersurface.comap_of_isOpenImmersionAtSource T.structMap hadm1
    (coverMap T h.valid) (MaxContactOpenCover.isLocalIsomorphism_coverMap T h.valid)
  have hA1 : ∀ m : ℕ, m = 1 →
      @IsMaxContactHypersurface T.base _ (coverTriple T h.valid).scheme
        (coverTriple T h.valid).structMap hftC
        (T.ideal.comap (coverMap T h.valid)) m
        ((AlgebraicGeometry.Scheme.Hom.ker e).comap (coverMap T h.valid)) := by
    rintro m rfl
    exact @isMaxContactHypersurface_of_eq_of_eq_of_eq T.base _ (coverTriple T h.valid).scheme
      (coverMap T h.valid ≫ T.structMap) (coverTriple T h.valid).structMap hcmp hftC
      (T.ideal.comap (coverMap T h.valid)) (T.ideal.comap (coverMap T h.valid))
      ((AlgebraicGeometry.Scheme.Hom.ker e).comap (coverMap T h.valid))
      ((AlgebraicGeometry.Scheme.Hom.ker e).comap (coverMap T h.valid)) 1
      (coverTriple_structureMorphism T h.valid).symm rfl rfl hkey
  have hbase := BoundarySeparationByMaxContact.isMaxContactHypersurface_coverMaxContactIdeal hstar P T h
  have htrm : ∀ m : ℕ, (coverTriple T h.valid).mult = m →
      IsMaxContactHypersurface (coverTriple T h.valid).base
        ((emptyMarkedBlowupSequenceData (coverTriple T h.valid).structMap (coverTriple T h.valid).ideal
            (coverTriple T h.valid).mult (coverTriple T h.valid).boundary).proj
          (emptyMarkedBlowupSequenceData (coverTriple T h.valid).structMap (coverTriple T h.valid).ideal
            (coverTriple T h.valid).mult (coverTriple T h.valid).boundary).length ≫
          (coverTriple T h.valid).structMap)
        ((emptyMarkedBlowupSequenceData (coverTriple T h.valid).structMap (coverTriple T h.valid).ideal
            (coverTriple T h.valid).mult (coverTriple T h.valid).boundary).ideal
          (emptyMarkedBlowupSequenceData (coverTriple T h.valid).structMap (coverTriple T h.valid).ideal
            (coverTriple T h.valid).mult (coverTriple T h.valid).boundary).length) m
        (MaxContactReduction.strictTransformAtLength
          (emptyMarkedBlowupSequenceData (coverTriple T h.valid).structMap (coverTriple T h.valid).ideal
            (coverTriple T h.valid).mult (coverTriple T h.valid).boundary)
          (coverMaxContactIdeal T h.valid)) := by
    rintro m rfl
    exact isMaxContactHypersurface_iteratedStrictTransform hstar (coverTriple T h.valid) hVcover hOcover
      (coverMaxContactIdeal T h.valid) hbase
      (emptyMarkedBlowupSequenceData (coverTriple T h.valid).structMap (coverTriple T h.valid).ideal
        (coverTriple T h.valid).mult (coverTriple T h.valid).boundary)
      (emptyMarkedBlowupSequenceData (coverTriple T h.valid).structMap (coverTriple T h.valid).ideal
        (coverTriple T h.valid).mult (coverTriple T h.valid).boundary).length le_rfl
  have hA2 : ∀ m : ℕ, m = 1 →
      @IsMaxContactHypersurface T.base _ (coverTriple T h.valid).scheme
        (coverTriple T h.valid).structMap hftC
        (T.ideal.comap (coverMap T h.valid)) m
        (MaxContactReduction.strictTransformAtLength
          (emptyMarkedBlowupSequenceData (coverTriple T h.valid).structMap (coverTriple T h.valid).ideal
            (coverTriple T h.valid).mult (coverTriple T h.valid).boundary)
          (coverMaxContactIdeal T h.valid)) := by
    rintro m rfl
    exact @isMaxContactHypersurface_of_eq_of_eq_of_eq T.base _ (coverTriple T h.valid).scheme
      ((emptyMarkedBlowupSequenceData (coverTriple T h.valid).structMap (coverTriple T h.valid).ideal
          (coverTriple T h.valid).mult (coverTriple T h.valid).boundary).proj
        (emptyMarkedBlowupSequenceData (coverTriple T h.valid).structMap (coverTriple T h.valid).ideal
          (coverTriple T h.valid).mult (coverTriple T h.valid).boundary).length ≫
        (coverTriple T h.valid).structMap)
      (coverTriple T h.valid).structMap hft hftC
      ((emptyMarkedBlowupSequenceData (coverTriple T h.valid).structMap (coverTriple T h.valid).ideal
          (coverTriple T h.valid).mult (coverTriple T h.valid).boundary).ideal
        (emptyMarkedBlowupSequenceData (coverTriple T h.valid).structMap (coverTriple T h.valid).ideal
          (coverTriple T h.valid).mult (coverTriple T h.valid).boundary).length)
      (T.ideal.comap (coverMap T h.valid))
      (MaxContactReduction.strictTransformAtLength
        (emptyMarkedBlowupSequenceData (coverTriple T h.valid).structMap (coverTriple T h.valid).ideal
          (coverTriple T h.valid).mult (coverTriple T h.valid).boundary)
        (coverMaxContactIdeal T h.valid))
      (MaxContactReduction.strictTransformAtLength
        (emptyMarkedBlowupSequenceData (coverTriple T h.valid).structMap (coverTriple T h.valid).ideal
          (coverTriple T h.valid).mult (coverTriple T h.valid).boundary)
        (coverMaxContactIdeal T h.valid)) 1
      (projectionToBase_emptyMarkedBlowupSequenceData_comp (coverTriple T h.valid))
      ((emptyMarkedBlowupSequenceData_ideal (coverTriple T h.valid).structMap (coverTriple T h.valid).ideal
        (coverTriple T h.valid).mult (coverTriple T h.valid).boundary
        (emptyMarkedBlowupSequenceData (coverTriple T h.valid).structMap (coverTriple T h.valid).ideal
          (coverTriple T h.valid).mult (coverTriple T h.valid).boundary).length).trans
        hcoverIdeal)
      rfl (htrm 1 hcoverMult)
  have hTdim : P ((T.withBoundary [AlgebraicGeometry.Scheme.Hom.ker e]).pullbackAlong
      (coverTriple T h.valid).scheme (coverTriple T h.valid).structMap
      (coverMap T h.valid)).krullDimSucc :=
    hmono _ _ (hstar.coverTriple_dim_le T h.valid) h.dim_prop
  have hTO : ∀ x : ↥(((T.withBoundary [AlgebraicGeometry.Scheme.Hom.ker e]).pullbackAlong
      (coverTriple T h.valid).scheme (coverTriple T h.valid).structMap
      (coverMap T h.valid)).scheme),
      orderAt (((T.withBoundary [AlgebraicGeometry.Scheme.Hom.ker e]).pullbackAlong
        (coverTriple T h.valid).scheme (coverTriple T h.valid).structMap
        (coverMap T h.valid)).ideal) x ≤
      (((((T.withBoundary [AlgebraicGeometry.Scheme.Hom.ker e]).pullbackAlong
        (coverTriple T h.valid).scheme (coverTriple T h.valid).structMap
        (coverMap T h.valid)).mult) : ℕ) : ℕ∞) := by
    intro x
    show orderAt (T.ideal.comap (coverMap T h.valid)) x ≤ ((T.mult : ℕ) : ℕ∞)
    rw [orderAt_comap T.base T.structMap (coverMap T h.valid) T.ideal x]
    exact h.orderLE _
  have hmultPB : (((T.withBoundary [AlgebraicGeometry.Scheme.Hom.ker e]).pullbackAlong
      (coverTriple T h.valid).scheme (coverTriple T h.valid).structMap
      (coverMap T h.valid)).mult) = 1 := hmult
  have hbdPB : (((T.withBoundary [AlgebraicGeometry.Scheme.Hom.ker e]).pullbackAlong
      (coverTriple T h.valid).scheme (coverTriple T h.valid).structMap
      (coverMap T h.valid)).boundary)
      = [(AlgebraicGeometry.Scheme.Hom.ker e).comap (coverMap T h.valid)] := rfl
  have hAdmEq := isomorphic_of_isMaxContactHypersurface_singleton_boundary hin P hmono (A 0) B (hspec 0)
    ((T.withBoundary [AlgebraicGeometry.Scheme.Hom.ker e]).pullbackAlong
      (coverTriple T h.valid).scheme (coverTriple T h.valid).structMap (coverMap T h.valid))
    hpb.1 hTdim hTO hmultPB
    ((AlgebraicGeometry.Scheme.Hom.ker e).comap (coverMap T h.valid))
    (MaxContactReduction.strictTransformAtLength
      (emptyMarkedBlowupSequenceData (coverTriple T h.valid).structMap (coverTriple T h.valid).ideal
        (coverTriple T h.valid).mult (coverTriple T h.valid).boundary)
      (coverMaxContactIdeal T h.valid))
    hbdPB hDU hV₂ (hA1 T.mult hmult) (hA2 T.mult hmult)
  have hEq : (coverMarkedBlowupData T h.valid hinv (MaxContactFunctoriality.lowerDimensionalFamily A T)).toSequenceOfBlowups.Isomorphic
      (A 0 (derivedTriple (coverTriple T h.valid)
        (emptyMarkedBlowupSequenceData (coverTriple T h.valid).structMap (coverTriple T h.valid).ideal
          (coverTriple T h.valid).mult (coverTriple T h.valid).boundary) hft
        [MaxContactReduction.strictTransformAtLength
          (emptyMarkedBlowupSequenceData (coverTriple T h.valid).structMap (coverTriple T h.valid).ideal
            (coverTriple T h.valid).mult (coverTriple T h.valid).boundary)
          (coverMaxContactIdeal T h.valid)]
        (coverTriple T h.valid).boundary.length)).toSequenceOfBlowups := by
    rw [heq]
    refine SequenceOfBlowups.Isomorphic.trans
      (isomorphic_of_emptyMarkedBlowupSequenceData_append (coverTriple T h.valid).structMap
        (coverTriple T h.valid).ideal (coverTriple T h.valid).mult
        (coverTriple T h.valid).boundary
        ((BlowupSequenceData.ofSequenceOfBlowups (A 0 (derivedTriple (coverTriple T h.valid)
            (emptyMarkedBlowupSequenceData (coverTriple T h.valid).structMap (coverTriple T h.valid).ideal
              (coverTriple T h.valid).mult (coverTriple T h.valid).boundary) hft
            [MaxContactReduction.strictTransformAtLength
              (emptyMarkedBlowupSequenceData (coverTriple T h.valid).structMap (coverTriple T h.valid).ideal
                (coverTriple T h.valid).mult (coverTriple T h.valid).boundary)
              (coverMaxContactIdeal T h.valid)]
            (coverTriple T h.valid).boundary.length)).toSequenceOfBlowups).toMarkedBlowupSequenceData
          ((emptyMarkedBlowupSequenceData (coverTriple T h.valid).structMap (coverTriple T h.valid).ideal
              (coverTriple T h.valid).mult (coverTriple T h.valid).boundary).proj
            (emptyMarkedBlowupSequenceData (coverTriple T h.valid).structMap (coverTriple T h.valid).ideal
              (coverTriple T h.valid).mult (coverTriple T h.valid).boundary).length ≫
            (coverTriple T h.valid).structMap)
          ((emptyMarkedBlowupSequenceData (coverTriple T h.valid).structMap (coverTriple T h.valid).ideal
              (coverTriple T h.valid).mult (coverTriple T h.valid).boundary).ideal
            (emptyMarkedBlowupSequenceData (coverTriple T h.valid).structMap (coverTriple T h.valid).ideal
              (coverTriple T h.valid).mult (coverTriple T h.valid).boundary).length)
          (coverTriple T h.valid).mult
          ((emptyMarkedBlowupSequenceData (coverTriple T h.valid).structMap (coverTriple T h.valid).ideal
              (coverTriple T h.valid).mult (coverTriple T h.valid).boundary).boundary
            (emptyMarkedBlowupSequenceData (coverTriple T h.valid).structMap (coverTriple T h.valid).ideal
              (coverTriple T h.valid).mult (coverTriple T h.valid).boundary).length) hmk)
        hinv) ?_
    exact BlowupSequenceData.ofSequenceOfBlowups_toSequenceOfBlowups_isomorphic _
  have hheq : HEq ((A 0 (derivedTriple (coverTriple T h.valid)
        (emptyMarkedBlowupSequenceData (coverTriple T h.valid).structMap (coverTriple T h.valid).ideal
          (coverTriple T h.valid).mult (coverTriple T h.valid).boundary) hft
        [MaxContactReduction.strictTransformAtLength
          (emptyMarkedBlowupSequenceData (coverTriple T h.valid).structMap (coverTriple T h.valid).ideal
            (coverTriple T h.valid).mult (coverTriple T h.valid).boundary)
          (coverMaxContactIdeal T h.valid)]
        (coverTriple T h.valid).boundary.length)).toSequenceOfBlowups)
      ((A 0 (((T.withBoundary [AlgebraicGeometry.Scheme.Hom.ker e]).pullbackAlong
          (coverTriple T h.valid).scheme (coverTriple T h.valid).structMap
          (coverMap T h.valid)).withBoundary
        [MaxContactReduction.strictTransformAtLength
          (emptyMarkedBlowupSequenceData (coverTriple T h.valid).structMap (coverTriple T h.valid).ideal
            (coverTriple T h.valid).mult (coverTriple T h.valid).boundary)
          (coverMaxContactIdeal T h.valid)])).toSequenceOfBlowups) := by
    rw [htri]
  have hcast := eq_of_heq hheq
  rw [hcast] at hEq
  exact hpb.2.of_isomorphic_pullback (hAdmEq.trans hEq.symm)

theorem isStrictPullbackBlowupSeq_coverMarkedBlowupData_of_isMaxContactHypersurface
    (hstar : MaxContactCoverProperties.{u}) (hin : OrderReduction.OrderReductionHypotheses.{u}) (hinv : ComapIsoInvariance.{u})
    (P : ℕ → Prop) (hmono : ∀ a b : ℕ, a ≤ b → P b → P a)
    (A : ℕ → PrincipalizationAssignment.{u}) (B : PrincipalizationAssignment.{u})
    (hspec : ∀ j : ℕ, IsBoundaryDivisorReduction P j (A j) B)
    (T : MarkedIdealWithBoundary.{u}) (h : MaxContactFunctoriality.OrderReductionHypotheses P T)
    (hbd : T.boundary = []) (hmult : T.mult = 1)
    {Y : Scheme.{u}} (e : Y ⟶ T.scheme) [AlgebraicGeometry.IsClosedImmersion e]
    (hadm : ∀ [AlgebraicGeometry.LocallyOfFiniteType T.structMap],
      IsMaxContactHypersurface T.base T.structMap T.ideal T.mult
        (AlgebraicGeometry.Scheme.Hom.ker e))
    (hV : (T.withBoundary [AlgebraicGeometry.Scheme.Hom.ker e]).IsAdmissible) :
    IsStrictPullbackBlowupSeq (coverMap T h.valid)
      (coverMarkedBlowupData T h.valid hinv (MaxContactFunctoriality.lowerDimensionalFamily A T)).toSequenceOfBlowups
      (A 0 (T.withBoundary [AlgebraicGeometry.Scheme.Hom.ker e])).toSequenceOfBlowups := by
  have hSb : (coverTriple T h.valid).boundary = [] :=
    (coverTriple_boundary T h.valid).trans
      ((congrArg
          (List.map (fun D : T.scheme.IdealSheafData => D.comap (coverMap T h.valid)))
          hbd).trans List.map_nil)
  have hSlen : (coverTriple T h.valid).boundary.length = 0 := congrArg List.length hSb
  have hs : BoundarySeparationByMaxContact.separateAllBoundary T h.valid hinv A
      = emptyMarkedBlowupSequenceData (coverTriple T h.valid).structMap (coverTriple T h.valid).ideal
          (coverTriple T h.valid).mult (coverTriple T h.valid).boundary := by
    show MaxContactReduction.separateBoundary hinv T (MaxContactFunctoriality.lowerDimensionalFamily A T)
        (coverTriple T h.valid) ((coverTriple T h.valid).boundary.length) = _
    rw [hSlen]
    exact separateBoundary_zero hinv T (MaxContactFunctoriality.lowerDimensionalFamily A T) _
  obtain ⟨hft, hVc, _, hmk, heq, _⟩ :=
    BoundarySeparationByMaxContact.exists_cover_eq_separateAllBoundary_append hstar hinv P hmono A B hspec T h
  exact isStrictPullbackBlowupSeq_cover_of_eq_append hstar hin hinv P hmono A B hspec T h hbd hmult
    e hadm hV (BoundarySeparationByMaxContact.separateAllBoundary T h.valid hinv A) hs hft hVc hmk heq

theorem isStrictPullbackBlowupSeq_coverMarkedBlowupData_of_etaleChart
    (hstar : MaxContactCoverProperties.{u}) (hin : OrderReduction.OrderReductionHypotheses.{u}) (hinv : ComapIsoInvariance.{u})
    (P : ℕ → Prop) (hmono : ∀ a b : ℕ, a ≤ b → P b → P a)
    (A : ℕ → PrincipalizationAssignment.{u}) (B : PrincipalizationAssignment.{u})
    (hspec : ∀ j : ℕ, IsBoundaryDivisorReduction P j (A j) B)
    (T : MarkedIdealWithBoundary.{u}) (h : MaxContactFunctoriality.OrderReductionHypotheses P T)
    (hbd : T.boundary = []) (hmult : T.mult = 1)
    {Y : Scheme.{u}} (e : Y ⟶ T.scheme) [AlgebraicGeometry.IsClosedImmersion e]
    (hchart : ∀ x : ↥T.scheme, x ∈ (AlgebraicGeometry.Scheme.Hom.ker e).support →
      ∃ (U : T.scheme.Opens) (n : ℕ) (c : EtaleChart T.structMap U n) (j : Fin n),
        x ∈ U ∧ restrictIdeal (AlgebraicGeometry.Scheme.Hom.ker e) U =
          c.coordIdeal ({j} : Finset (Fin n)))
    (hle : AlgebraicGeometry.Scheme.Hom.ker e ≤ T.ideal)
    (hV : (T.withBoundary [AlgebraicGeometry.Scheme.Hom.ker e]).IsAdmissible) :
    IsStrictPullbackBlowupSeq (coverMap T h.valid)
      (coverMarkedBlowupData T h.valid hinv (MaxContactFunctoriality.lowerDimensionalFamily A T)).toSequenceOfBlowups
      (A 0 (T.withBoundary [AlgebraicGeometry.Scheme.Hom.ker e])).toSequenceOfBlowups := by
  have := h.valid.locallyOfFiniteType
  have := h.valid.smooth
  have : CharZero T.base := h.valid.charZero
  refine isStrictPullbackBlowupSeq_coverMarkedBlowupData_of_isMaxContactHypersurface hstar hin hinv P hmono A B hspec T h hbd
    hmult e ?_ hV
  intro hftinst
  have : AlgebraicGeometry.LocallyOfFiniteType T.structMap := hftinst
  rw [hmult]
  exact isMaxContactHypersurface_one_of_etaleChart T.structMap T.ideal
    (AlgebraicGeometry.Scheme.Hom.ker e) hchart hle

theorem isStrictPullbackBlowupSeq_coverMarkedBlowupData_of_isSmoothDivisor
    (hstar : MaxContactCoverProperties.{u}) (hin : OrderReduction.OrderReductionHypotheses.{u}) (hinv : ComapIsoInvariance.{u})
    (P : ℕ → Prop) (hmono : ∀ a b : ℕ, a ≤ b → P b → P a)
    (A : ℕ → PrincipalizationAssignment.{u}) (B : PrincipalizationAssignment.{u})
    (hspec : ∀ j : ℕ, IsBoundaryDivisorReduction P j (A j) B)
    (T : MarkedIdealWithBoundary.{u}) (h : MaxContactFunctoriality.OrderReductionHypotheses P T)
    (hbd : T.boundary = []) (hmult : T.mult = 1)
    {Y : Scheme.{u}} (e : Y ⟶ T.scheme) [AlgebraicGeometry.IsClosedImmersion e]
    (hdiv : IsSmoothDivisor T.structMap (AlgebraicGeometry.Scheme.Hom.ker e))
    (J : Y.IdealSheafData) (hJ : T.ideal = imageIdealSheaf e J)
    (hV : (T.withBoundary [AlgebraicGeometry.Scheme.Hom.ker e]).IsAdmissible) :
    IsStrictPullbackBlowupSeq (coverMap T h.valid)
      (coverMarkedBlowupData T h.valid hinv (MaxContactFunctoriality.lowerDimensionalFamily A T)).toSequenceOfBlowups
      (A 0 (T.withBoundary [AlgebraicGeometry.Scheme.Hom.ker e])).toSequenceOfBlowups := by
  have := h.valid.locallyOfFiniteType
  have := h.valid.smooth
  have : CharZero T.base := h.valid.charZero
  refine isStrictPullbackBlowupSeq_coverMarkedBlowupData_of_etaleChart hstar hin hinv P hmono A B hspec T h hbd hmult
    e ?_ ?_ hV
  · intro x hx
    exact exists_etaleChart_restrictIdeal_eq_coordIdeal_singleton T.structMap
      (AlgebraicGeometry.Scheme.Hom.ker e) hdiv x hx
  · rw [hJ, imageIdealSheaf_eq_ker]
    intro U
    exact AlgebraicGeometry.Scheme.Hom.le_ker_comp ..

end MaxContactCoverData

end FunctorialResolution.EmbeddedResolution
