import Mathlib
import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.NoetherianBlowup
import Development.ResolutionOfSingularities.EmbeddedResolution.StrictTransformCharts.StrictNormalCrossingsEraseMember
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.StrictNormalCrossings
import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.DerivBalancedOrderLocus
import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.IdealSheafOrder
import Development.ResolutionOfSingularities.EmbeddedResolution.MaximalContactHypersurfaces.MaxContactIdeal
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReductionProperties
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.DivisorReductionSequence
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.DivisorReductionStepProperties
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.AmbientBlowupSequence
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.DivisorReduction.LowerBoundaryData
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.IdealBlowupSequence
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.MarkedSequenceOfBlowups
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.SupportsAlongSequence
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.SmoothComponentsDisjoint
import Development.ResolutionOfSingularities.Foundations.BlowupUniversalProperty
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionOfSingularities
universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace

noncomputable section

namespace FunctorialResolution.EmbeddedResolution

theorem isClopen_of_pairwise_disjoint_irreducibleComponents {S : Type*} [TopologicalSpace S]
    [NoetherianSpace S]
    (hsep : ∀ C₁ ∈ irreducibleComponents S, ∀ C₂ ∈ irreducibleComponents S,
      C₁ ≠ C₂ → Disjoint C₁ C₂)
    {K : Set S} (hK : K ∈ irreducibleComponents S) : IsClopen K := by
  have hKc : IsClosed K := isClosed_of_mem_irreducibleComponents K hK
  have hcompl : Kᶜ = ⋃₀ (irreducibleComponents S \ {K}) := by
    ext x
    constructor
    · intro hx
      refine ⟨irreducibleComponent x, ⟨irreducibleComponent_mem_irreducibleComponents .., ?_⟩, ?_⟩
      · simp only [Set.mem_singleton_iff]
        intro h
        exact hx (by rw [← h]; exact (irreducibleComponent_property x).2.1 rfl)
      · exact (irreducibleComponent_property x).2.1 rfl
    · rintro ⟨C, ⟨hC, hCK⟩, hxC⟩ hxK
      have hne : C ≠ K := by
        intro h
        exact hCK (by simp [h])
      exact Set.disjoint_left.mp (hsep C hC K hK hne) hxC hxK
  have hfin : (irreducibleComponents S \ {K}).Finite :=
    Set.Finite.subset NoetherianSpace.finite_irreducibleComponents Set.sdiff_subset
  refine ⟨hKc, ?_⟩
  rw [← isClosed_compl_iff, hcompl, Set.sUnion_eq_biUnion]
  exact hfin.isClosed_biUnion (fun C hC => isClosed_of_mem_irreducibleComponents C hC.1)

theorem connectedComponent_subset_of_mem_irreducibleComponents {S : Type*} [TopologicalSpace S]
    [NoetherianSpace S]
    (hsep : ∀ C₁ ∈ irreducibleComponents S, ∀ C₂ ∈ irreducibleComponents S,
      C₁ ≠ C₂ → Disjoint C₁ C₂)
    {K : Set S} (hK : K ∈ irreducibleComponents S) {x : S} (hx : x ∈ K) :
    connectedComponent x ⊆ K :=
  (isClopen_of_pairwise_disjoint_irreducibleComponents hsep hK).connectedComponent_subset hx

namespace DivisorReduction

private theorem smooth_subschemeι_comp_structureMorphism (T : MarkedIdealWithBoundary.{u}) (hV : T.IsAdmissible) (j : ℕ)
    (hj : j < T.boundary.length) :
    AlgebraicGeometry.Smooth ((T.boundary.get ⟨j, hj⟩).subschemeι ≫ T.structMap) := by
  have hmem : T.boundary.get ⟨j, hj⟩ ∈ T.boundary := List.getElem_mem hj
  have hDiv : IsSmoothDivisor T.structMap (T.boundary.get ⟨j, hj⟩) :=
    ((inStrictNormalCrossingPosition_iff T.structMap T.boundary).mp hV.snc).1 _ hmem
  exact ((isSmoothDivisor_iff _ _).mp hDiv).2

private theorem noetherianSpace_boundary_subscheme (T : MarkedIdealWithBoundary.{u}) (hV : T.IsAdmissible)
    (j : ℕ) (hj : j < T.boundary.length) :
    NoetherianSpace ↥(T.boundary.get ⟨j, hj⟩).subscheme := by
  have := hV.isNoetherian
  have : NoetherianSpace ↥T.scheme := inferInstance
  exact (AlgebraicGeometry.IsClosedImmersion.isClosedEmbedding
    (T.boundary.get ⟨j, hj⟩).subschemeι).isInducing.noetherianSpace

private theorem ker_ι_comp_ne_top {X Z : Scheme.{u}} (hX : NoetherianSpace ↥X) (V : X.Opens)
    (g : X ⟶ Z) (x : ↥X) (hx : x ∈ V) :
    AlgebraicGeometry.Scheme.Hom.ker (V.ι ≫ g) ≠ ⊤ := by
  have := hX
  have : NoetherianSpace ↥V.toScheme := inferInstanceAs (NoetherianSpace ↥(V : Set ↥X))
  intro h
  have : AlgebraicGeometry.QuasiCompact (V.ι ≫ g) := ⟨fun _ _ _ => NoetherianSpace.isCompact _⟩
  have hx' : x ∈ Set.range ⇑V.ι := by simpa using hx
  obtain ⟨y, hy⟩ := hx'
  have h3 : ⇑g x ∈ ((AlgebraicGeometry.Scheme.Hom.ker (V.ι ≫ g)).support : Set ↥Z) := by
    rw [AlgebraicGeometry.Scheme.Hom.support_ker]
    exact subset_closure ⟨y, by simp [hy]⟩
  rw [h] at h3
  simp at h3

theorem nonzeroOnComponents_comap_lowerIdealWithoutBlowup (T : MarkedIdealWithBoundary.{u}) (hV : T.IsAdmissible)
    (hBalanced : T.IsBalanced hV.locallyOfFiniteType) (j : ℕ) (hj : j < T.boundary.length)
    (hZ : DivisorReduction.containedComponentsIdeal T j hj = ⊤) :
    NonzeroOnComponents
      ((DivisorReduction.lowerIdealWithoutBlowup T).comap (T.boundary.get ⟨j, hj⟩).subschemeι) := by
  classical
  have := hV.charZero
  have := hV.smooth
  have := hV.locallyOfFiniteType
  have hsm : AlgebraicGeometry.Smooth ((T.boundary.get ⟨j, hj⟩).subschemeι ≫ T.structMap) :=
    smooth_subschemeι_comp_structureMorphism T hV j hj
  have hNoe : NoetherianSpace ↥(T.boundary.get ⟨j, hj⟩).subscheme :=
    noetherianSpace_boundary_subscheme T hV j hj
  have := hNoe
  have hbal : IsDerivBalanced T.base T.structMap T.ideal T.mult := hBalanced
  have hcs : orderAtLeastLocus T.ideal T.mult = (T.ideal.support : Set ↥T.scheme) :=
    orderAtLeastLocus_eq_support_of_isDerivBalanced T.base T.structMap T.ideal T.mult hbal hV.one_le_mult
  have hdisj : ∀ C₁ ∈ irreducibleComponents ↥(T.boundary.get ⟨j, hj⟩).subscheme,
      ∀ C₂ ∈ irreducibleComponents ↥(T.boundary.get ⟨j, hj⟩).subscheme,
      C₁ ≠ C₂ → Disjoint C₁ C₂ :=
    irreducibleComponentsDisjointOfSmooth T.base (T.boundary.get ⟨j, hj⟩).subscheme
      ((T.boundary.get ⟨j, hj⟩).subschemeι ≫ T.structMap) hsm
  have hopen := isOpen_setOf_connectedComponent_subset_orderAtLeastLocus T hV j hj
  rw [DivisorReduction.containedComponentsIdeal_eq_ker T j hj hopen] at hZ
  have hI : DivisorReduction.lowerIdealWithoutBlowup T = T.ideal := by
    show T.ideal.comap (𝟙 T.scheme) = T.ideal
    simp
  rw [hI, nonzeroOnComponents_iff]
  intro C hC hsub
  obtain ⟨x, hxC⟩ := hC.1.nonempty
  have hCsub : C ⊆ ⇑(T.boundary.get ⟨j, hj⟩).subschemeι ⁻¹' orderAtLeastLocus T.ideal T.mult := by
    intro y hy
    have h1 : y ∈ ((T.ideal.comap (T.boundary.get ⟨j, hj⟩).subschemeι).support :
        Set ↥(T.boundary.get ⟨j, hj⟩).subscheme) := hsub hy
    rw [Set.mem_preimage, hcs]
    simpa [AlgebraicGeometry.Scheme.IdealSheafData.support_comap] using h1
  have hxV : connectedComponent x ⊆
      ⇑(T.boundary.get ⟨j, hj⟩).subschemeι ⁻¹' orderAtLeastLocus T.ideal T.mult :=
    fun z hz => hCsub (connectedComponent_subset_of_mem_irreducibleComponents hdisj hC hxC hz)
  exact absurd hZ (ker_ι_comp_ne_top hNoe _ _ x hxV)

theorem isAdmissible_restrictToDivisor (T : MarkedIdealWithBoundary.{u}) (hV : T.IsAdmissible)
    (_hOB : T.IsOrderBoundedByMult) (hBalanced : T.IsBalanced hV.locallyOfFiniteType) (j : ℕ)
    (hj : j < T.boundary.length) (hZ : DivisorReduction.containedComponentsIdeal T j hj = ⊤) :
    (DivisorReduction.restrictToDivisor T j hj).IsAdmissible := by
  have := hV.charZero
  have := hV.smooth
  have := hV.locallyOfFiniteType
  have := hV.quasiCompact
  have hsm : AlgebraicGeometry.Smooth ((T.boundary.get ⟨j, hj⟩).subschemeι ≫ T.structMap) :=
    smooth_subschemeι_comp_structureMorphism T hV j hj
  have := hsm
  have hlft : AlgebraicGeometry.LocallyOfFiniteType
      ((T.boundary.get ⟨j, hj⟩).subschemeι ≫ T.structMap) := inferInstance
  have hqc : AlgebraicGeometry.QuasiCompact
      ((T.boundary.get ⟨j, hj⟩).subschemeι ≫ T.structMap) := inferInstance
  have hsnc0 : InStrictNormalCrossingPosition ((T.boundary.get ⟨j, hj⟩).subschemeι ≫ T.structMap)
      ((T.boundary.eraseIdx j).map fun D => D.comap (T.boundary.get ⟨j, hj⟩).subschemeι) :=
    inStrictNormalCrossingPosition_comap_subschemeι_eraseIdx T.structMap T.boundary hV.snc j hj
  have hbd : DivisorReduction.lowerBoundaryWithoutBlowup T = T.boundary := by
    show List.map (fun D => D.comap (𝟙 T.scheme)) T.boundary = T.boundary
    simp
  have hsnc : InStrictNormalCrossingPosition ((T.boundary.get ⟨j, hj⟩).subschemeι ≫ T.structMap)
      (List.map (fun D => D.comap (T.boundary.get ⟨j, hj⟩).subschemeι)
        (List.take (T.boundary.length - 1) ((DivisorReduction.lowerBoundaryWithoutBlowup T).eraseIdx j))) := by
    rw [hbd, List.take_of_length_le (le_of_eq (List.length_eraseIdx_of_lt hj))]
    exact hsnc0
  exact ⟨hV.charZero, hlft,
    nonzeroOnComponents_comap_lowerIdealWithoutBlowup T hV hBalanced j hj hZ, hV.one_le_mult, hqc, hsm, hsnc⟩

end DivisorReduction

end FunctorialResolution.EmbeddedResolution

end
