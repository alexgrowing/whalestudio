import Mathlib
import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.NoetherianBlowup
import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.BlowupSequenceBasic
import Development.ResolutionOfSingularities.EmbeddedResolution.StrictTransformCharts.BlowupSmoothness
import Development.ResolutionOfSingularities.EmbeddedResolution.StrictTransformCharts.StrictNormalCrossingsBlowup
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.CoordinateDivisorSmoothness
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.StrictNormalCrossings
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.IdealBlowupSequence
import Development.ResolutionOfSingularities.Foundations.BlowupUniversalProperty
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionOfSingularities
universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace

noncomputable section

namespace FunctorialResolution.EmbeddedResolution

theorem inStrictNormalCrossingPositionAt_comap_iso {X X₀ : Scheme.{u}} {k : Type u} [Field k]
    (p : X ⟶ Spec (CommRingCat.of k)) (e : X₀ ≅ X) (E : List X.IdealSheafData) (x₀ : X₀)
    (h : InStrictNormalCrossingPositionAt p E (e.hom.base x₀)) :
    InStrictNormalCrossingPositionAt (e.hom ≫ p) (E.map (fun D => D.comap e.hom)) x₀ := by
  obtain ⟨U, hxU, m, c, a, h1, h2, h3⟩ := h.exists_etaleChart
  have hiso : IsIso (e.hom.resLE U (e.hom ⁻¹ᵁ U) le_rfl) := by
    rw [Scheme.Hom.resLE_eq_morphismRestrict]; infer_instance
  have hcet : AlgebraicGeometry.Etale c.map := c.isEtale
  have hAet : AlgebraicGeometry.Etale (e.hom.resLE U (e.hom ⁻¹ᵁ U) le_rfl) := inferInstance
  have hmem : x₀ ∈ e.hom ⁻¹ᵁ U := hxU
  refine inStrictNormalCrossingPositionAt_of_exists_etaleChart
    ⟨e.hom ⁻¹ᵁ U, hmem, m,
      ⟨e.hom.resLE U (e.hom ⁻¹ᵁ U) le_rfl ≫ c.map, ?_, inferInstance⟩, a, ?_, ?_, ?_⟩
  · rw [Category.assoc, c.comp_struct, ← Category.assoc, Scheme.Hom.resLE_comp_ι, Category.assoc]
  · intro i hi j hj t hit hjt
    exact h1 i (by simpa using hi) j (by simpa using hj) t hit hjt
  · intro i hi hnone
    have hi' : i < E.length := by simpa using hi
    have hget : (E.map (fun D => D.comap e.hom))[i]'hi = (E[i]'hi').comap e.hom := by simp
    rw [hget,
      restrictIdeal_comap_eq_comap_resLE_restrictIdeal e.hom (E[i]'hi') U (e.hom ⁻¹ᵁ U) le_rfl,
      h2 i hi' hnone]
    simp
  · intro i hi t hit
    have hi' : i < E.length := by simpa using hi
    have key : restrictIdeal ((E[i]'hi').comap e.hom) (e.hom ⁻¹ᵁ U)
        = (coordSubspaceIdeal k m {t}).comap
            (e.hom.resLE U (e.hom ⁻¹ᵁ U) le_rfl ≫ c.map) := by
      rw [restrictIdeal_comap_eq_comap_resLE_restrictIdeal e.hom (E[i]'hi') U (e.hom ⁻¹ᵁ U) le_rfl,
        h3 i hi' t hit, EtaleChart.coordIdeal_eq_comap_coordSubspaceIdeal, ← Scheme.IdealSheafData.comap_comp]
    have hget : (E.map (fun D => D.comap e.hom))[i]'hi = (E[i]'hi').comap e.hom := by simp
    rw [hget]
    exact key

theorem inStrictNormalCrossingPosition_comp_iso_hom {X X₀ : Scheme.{u}} {k : Type u} [Field k]
    (p : X ⟶ Spec (CommRingCat.of k)) (e : X₀ ≅ X) (E : List X.IdealSheafData)
    (h : InStrictNormalCrossingPosition p E) :
    InStrictNormalCrossingPosition (e.hom ≫ p) (E.map (fun D => D.comap e.hom)) := by
  obtain ⟨-, hpt⟩ := (inStrictNormalCrossingPosition_iff p E).mp h
  refine (inStrictNormalCrossingPosition_iff _ _).mpr
    ⟨?_, fun x₀ => inStrictNormalCrossingPositionAt_comap_iso p e E x₀ (hpt (e.hom.base x₀))⟩
  intro D hD
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hD
  refine isSmoothDivisor_of_locally_coordIdeal _ ?_
  intro x
  obtain ⟨U₀, hxU₀, n, c₀, a, k1, k2, k3⟩ :=
    (inStrictNormalCrossingPositionAt_comap_iso p e E x (hpt (e.hom.base x))).exists_etaleChart
  refine ⟨U₀, hxU₀, n, c₀, ?_⟩
  rcases hai : a i with _ | t
  · exact Or.inl (k2 i hi hai)
  · exact Or.inr ⟨t, k3 i hi t hai⟩

namespace IdealBlowupSequence

variable {k : Type u} [Field k] {X : Scheme.{u}} {p : X ⟶ Spec (CommRingCat.of k)}
  {I : X.IdealSheafData} {E : List X.IdealSheafData}

theorem structureMorphism_zero (s : IdealBlowupSequence p I E) :
    s.structureMorphism 0 = s.toSequenceOfBlowups.isoZero.hom ≫ p := by
  rw [structureMorphism_def, SequenceOfBlowups.projectionToBase_zero]

theorem structureMorphism_succ (s : IdealBlowupSequence p I E) (i : ℕ) :
    s.structureMorphism (i + 1) = s.toSequenceOfBlowups.transitionMapSucc i ≫ s.structureMorphism i := by
  rw [structureMorphism_def, structureMorphism_def, SequenceOfBlowups.blowupMorphism_eq_transitionMap, ← Category.assoc,
    SequenceOfBlowups.transitionMap_comp_projectionToBase]

theorem smooth_structureMorphism [AlgebraicGeometry.Smooth p] (s : IdealBlowupSequence p I E) (i : ℕ)
    (hi : i ≤ s.toSequenceOfBlowups.length) :
    AlgebraicGeometry.Smooth (s.structureMorphism i) := by
  revert hi
  induction i with
  | zero =>
    intro _
    rw [structureMorphism_zero]
    infer_instance
  | succ n ih =>
    intro hi
    have hn : n < s.toSequenceOfBlowups.length := hi
    have := ih (le_of_lt hn)
    rw [structureMorphism_succ]
    exact smooth_comp_of_isBlowupAlongIdealSheaf (s.hasStrictNormalCrossingsWith_center n hn)
      (s.toSequenceOfBlowups.isBlowupAlongIdealSheaf_blowupMorphism n hn)

theorem inStrictNormalCrossingPosition_boundary [AlgebraicGeometry.Smooth p] (s : IdealBlowupSequence p I E)
    (hE : InStrictNormalCrossingPosition p E)
    (hN : ∀ i, i ≤ s.toSequenceOfBlowups.length → NoetherianSpace ↥(s.toSequenceOfBlowups.schemeAt i)) :
    ∀ i, i ≤ s.toSequenceOfBlowups.length → InStrictNormalCrossingPosition (s.structureMorphism i) (s.boundary i) := by
  intro i
  induction i with
  | zero =>
    intro _
    have hb : s.boundary 0 = E.map (fun D => D.comap s.toSequenceOfBlowups.isoZero.hom) := by
      rw [s.boundary_zero, SequenceOfBlowups.projectionToBase_zero]
    rw [hb, structureMorphism_zero]
    exact inStrictNormalCrossingPosition_comp_iso_hom p s.toSequenceOfBlowups.isoZero E hE
  | succ n ih =>
    intro hi
    have hn : n < s.toSequenceOfBlowups.length := hi
    have : NoetherianSpace ↥(s.toSequenceOfBlowups.schemeAt (n + 1)) := hN (n + 1) hi
    have key := inStrictNormalCrossingPosition_strictTransform_append (s.structureMorphism n)
      (s.toSequenceOfBlowups.transitionMapSucc n) (s.toSequenceOfBlowups.center n) (s.boundary n)
      (s.toSequenceOfBlowups.isBlowupAlongIdealSheaf_blowupMorphism n hn) (ih (le_of_lt hn))
      (s.hasStrictNormalCrossingsWith_center n hn)
    rw [structureMorphism_succ, s.boundary_succ_eq_map_strictTransform_append n hn]
    exact key

theorem isNoetherian_schemeAt [AlgebraicGeometry.IsNoetherian X] (s : IdealBlowupSequence p I E) (i : ℕ)
    (hi : i ≤ s.toSequenceOfBlowups.length) :
    AlgebraicGeometry.IsNoetherian (s.toSequenceOfBlowups.schemeAt i) :=
  EmbeddedResolution.isNoetherian_schemeAt s.toSequenceOfBlowups i hi

theorem inStrictNormalCrossingPosition_boundary_of_isNoetherian [AlgebraicGeometry.Smooth p]
    [AlgebraicGeometry.IsNoetherian X] (s : IdealBlowupSequence p I E) (hE : InStrictNormalCrossingPosition p E) :
    ∀ i, i ≤ s.toSequenceOfBlowups.length → InStrictNormalCrossingPosition (s.structureMorphism i) (s.boundary i) := by
  refine inStrictNormalCrossingPosition_boundary s hE ?_
  intro i hi
  have := s.isNoetherian_schemeAt i hi
  infer_instance

end IdealBlowupSequence

end FunctorialResolution.EmbeddedResolution

end
