import Mathlib
import Development.ResolutionOfSingularities.Foundations.Blowup.BlowupProperties
import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.ClopenRestriction
import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.NoetherianBlowup
import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.StrictTransform
import Development.ResolutionOfSingularities.Foundations.Blowup.StrictTransform
import Development.ResolutionOfSingularities.EmbeddedResolution.StrictTransformCharts.TotalTransform
import Development.ResolutionOfSingularities.EmbeddedResolution.StrictTransformCharts.CoordinateBlowupChart
import Development.ResolutionOfSingularities.EmbeddedResolution.StrictTransformCharts.StrictTransformSubscheme
import Development.ResolutionOfSingularities.EmbeddedResolution.StrictTransformCharts.StrictNormalCrossingsBlowup
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.StrictNormalCrossings
import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.IdealSheafOrder
import Development.ResolutionOfSingularities.Foundations.Schemes.AffineOpens
import Development.ResolutionOfSingularities.EmbeddedResolution.AlgebraicPreliminaries.GenericPointImage
import Development.ResolutionOfSingularities.EmbeddedResolution.MaximalContactHypersurfaces.TunedSheaf
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReductionProperties
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MonomialCase.MonomialPrincipalization
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MonomialCase.StrictTransformComponents
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MonomialCase.ComponentUnionIdeal
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MonomialCase.CoordinateSubspaceIdeal
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MonomialCase.IntersectionComponents
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MonomialCase.MonomialGeometryHypotheses
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.IdealBlowupSequence
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.MarkedSequenceOfBlowups
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.SupportsAlongSequence
import Development.ResolutionOfSingularities.Foundations.BlowupUniversalProperty
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionOfSingularities
universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace

noncomputable section

namespace FunctorialResolution.EmbeddedResolution

private theorem getElem_map_strictTransform_append_of_lt {X' X : Scheme.{u}} (π : X' ⟶ X) (Z : X.IdealSheafData)
    (L : List X.IdealSheafData) (i : ℕ) (hi : i < L.length)
    (hi' : i < (L.map (Blowup.strictTransform π Z) ++ [Blowup.exceptionalIdeal π Z]).length) :
    (L.map (Blowup.strictTransform π Z) ++ [Blowup.exceptionalIdeal π Z])[i]'hi'
      = Blowup.strictTransform π Z (L[i]'hi) := by
  have h1 : i < (L.map (Blowup.strictTransform π Z)).length := by
    rw [List.length_map]; exact hi
  exact (List.getElem_append_left h1).trans (List.getElem_map _)

private theorem getElem_length_map_strictTransform_append {X' X : Scheme.{u}} (π : X' ⟶ X) (Z : X.IdealSheafData)
    (L : List X.IdealSheafData)
    (hi' : L.length < (L.map (Blowup.strictTransform π Z) ++ [Blowup.exceptionalIdeal π Z]).length) :
    (L.map (Blowup.strictTransform π Z) ++ [Blowup.exceptionalIdeal π Z])[L.length]'hi'
      = Blowup.exceptionalIdeal π Z := by
  simp [List.getElem_append_right]

theorem transformedBoundary_get_strictTransformIndex {X' X : Scheme.{u}} (π : X' ⟶ X) (Z : X.IdealSheafData)
    (L : List X.IdealSheafData) (j : Fin L.length) :
    (transformedBoundary π Z L).get (strictTransformIndex π Z L j) = Blowup.strictTransform π Z (L.get j) := by
  simp only [List.get_eq_getElem]
  exact getElem_map_strictTransform_append_of_lt π Z L (j : ℕ) j.isLt _

theorem mem_support_intersectionIdeal_iff {Y : Scheme.{u}} (L : List Y.IdealSheafData)
    (J : Finset (Fin L.length)) (y : ↥Y) :
    y ∈ (intersectionIdeal L J).support ↔ ∀ j ∈ J, y ∈ (L.get j).support := by
  have hsup : ∀ A B : Y.IdealSheafData,
      y ∈ (A ⊔ B).support ↔ y ∈ A.support ∧ y ∈ B.support := by
    intro A B
    rw [Scheme.IdealSheafData.support_sup]
    exact Iff.rfl
  rw [intersectionIdeal_eq_iSup]
  induction J using Finset.induction_on with
  | empty =>
      have hbot : (⨆ j ∈ (∅ : Finset (Fin L.length)), L.get j) = ⊥ := by simp
      rw [hbot]
      constructor
      · intro _ j hj
        exact absurd hj (Finset.notMem_empty j)
      · intro _
        rw [mem_support_iff_stalkIdeal_le_maximalIdeal, stalkIdeal_bot]
        exact bot_le
  | insert a s _ ih =>
      rw [Finset.iSup_insert, hsup, Finset.forall_mem_insert]
      exact and_congr_right fun _ => ih

theorem mem_support_strictTransform_iff_of_notMem_support {X X' : Scheme.{u}}
    [IsLocallyNoetherian X'] (π : X' ⟶ X) (Z D : X.IdealSheafData) (x' : ↥X')
    (hx' : π x' ∉ Z.support) :
    x' ∈ (Blowup.strictTransform π Z D).support ↔ π x' ∈ D.support := by
  have hsupp : ((Blowup.strictTransform π Z D).support : Set ↥X') =
      closure (⇑π.base ⁻¹' ((D.support : Set ↥X) \ (Z.support : Set ↥X))) :=
    support_strictTransform_eq_closure_preimage π Z D
  constructor
  · intro hx
    have h1 : x' ∈ closure (⇑π.base ⁻¹' ((D.support : Set ↥X) \ (Z.support : Set ↥X))) := by
      have h0 : x' ∈ ((Blowup.strictTransform π Z D).support : Set ↥X') := hx
      rw [hsupp] at h0
      exact h0
    have h2 : closure (⇑π.base ⁻¹' ((D.support : Set ↥X) \ (Z.support : Set ↥X)))
        ⊆ ⇑π.base ⁻¹' ((D.support : Set ↥X)) := by
      refine closure_minimal (fun y hy => hy.1) ?_
      exact (Scheme.IdealSheafData.support D).isClosed.preimage π.base.hom.continuous
    exact h2 h1
  · intro hx
    have h3 : x' ∈ ⇑π.base ⁻¹' ((D.support : Set ↥X) \ (Z.support : Set ↥X)) := ⟨hx, hx'⟩
    have h4 := subset_closure h3
    rw [← hsupp] at h4
    exact h4

theorem mem_support_intersectionIdeal_transformedBoundary_iff (T : MarkedIdealWithBoundary.{u}) (X' : Scheme.{u})
    (π : X' ⟶ T.scheme) (Z : T.scheme.IdealSheafData)
    (J : Finset (Fin T.boundary.length)) (x' : ↥X') :
    x' ∈ (intersectionIdeal (transformedBoundary π Z T.boundary)
            (Finset.image (strictTransformIndex π Z T.boundary) J)).support ↔
      ∀ j ∈ J, x' ∈ (Blowup.strictTransform π Z (T.boundary.get j)).support := by
  rw [mem_support_intersectionIdeal_iff]
  constructor
  · intro h j hj
    have h1 := h (strictTransformIndex π Z T.boundary j) (Finset.mem_image_of_mem _ hj)
    rwa [transformedBoundary_get_strictTransformIndex] at h1
  · intro h j' hj'
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hj'
    rw [transformedBoundary_get_strictTransformIndex]
    exact h j hj

private theorem mem_support_intersectionIdeal_transformedBoundary_iff_of_notMem {X X' : Scheme.{u}} [IsLocallyNoetherian X']
    (π : X' ⟶ X) (Z : X.IdealSheafData) (L : List X.IdealSheafData)
    (J : Finset (Fin L.length)) (x' : ↥X') (hx' : π x' ∉ Z.support) :
    x' ∈ (intersectionIdeal (transformedBoundary π Z L) (J.image (strictTransformIndex π Z L))).support ↔
      π x' ∈ (intersectionIdeal L J).support := by
  rw [mem_support_intersectionIdeal_iff, mem_support_intersectionIdeal_iff]
  constructor
  · intro h j hj
    have h1 := h (strictTransformIndex π Z L j) (Finset.mem_image_of_mem _ hj)
    rw [transformedBoundary_get_strictTransformIndex] at h1
    exact (mem_support_strictTransform_iff_of_notMem_support π Z (L.get j) x' hx').mp h1
  · intro h j' hj'
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hj'
    rw [transformedBoundary_get_strictTransformIndex]
    exact (mem_support_strictTransform_iff_of_notMem_support π Z (L.get j) x' hx').mpr (h j hj)

private theorem genericPoint_notMem_support_exceptionalIdeal
    (T : MarkedIdealWithBoundary.{u}) (Z : T.scheme.IdealSheafData)
    (hsncZ : HasStrictNormalCrossingsWith T.structMap Z T.boundary)
    (X' : Scheme.{u}) (π : X' ⟶ T.scheme) (hπ : Blowup.IsBlowupAlongIdealSheaf π Z)
    [IsLocallyNoetherian X'] [NoetherianSpace ↥X']
    (J : Finset (Fin T.boundary.length)) (C' : Set ↥X')
    (hC'irr : IsIrreducible C')
    (hC'sub : C' ⊆ (↑(intersectionIdeal (transformedBoundary π Z T.boundary)
        (J.image (strictTransformIndex π Z T.boundary))).support : Set ↥X'))
    (hC'max : ∀ D : Set ↥X', IsIrreducible D → C' ⊆ D →
        D ⊆ (↑(intersectionIdeal (transformedBoundary π Z T.boundary)
          (J.image (strictTransformIndex π Z T.boundary))).support : Set ↥X') → D = C')
    (ξ' : ↥X') (hξ' : IsGenericPoint ξ' C') :
    ξ' ∉ (Blowup.exceptionalIdeal π Z).support := by
  intro hmem
  have hπξ : π ξ' ∈ Z.support := by
    have h0 : ξ' ∈ (↑(Z.comap π).support : Set ↥X') := hmem
    rw [support_comap_eq π Z] at h0
    exact h0
  have hξ'A' : ξ' ∈ (intersectionIdeal (transformedBoundary π Z T.boundary)
      (J.image (strictTransformIndex π Z T.boundary))).support := hC'sub hξ'.mem
  have hpos := inStrictNormalCrossingPositionAt_strictTransform_of_mem_support
    T.structMap π Z T.boundary hπ hsncZ ξ' hπξ
  obtain ⟨U, hξU, m, c, a, hinj, hnone, hsome⟩ := hpos
  have hlen : (T.boundary.map (Blowup.strictTransform π Z) ++ [Blowup.exceptionalIdeal π Z]).length
      = T.boundary.length + 1 := by simp
  have hnlt : T.boundary.length
      < (T.boundary.map (Blowup.strictTransform π Z) ++ [Blowup.exceptionalIdeal π Z]).length := by
    rw [hlen]; exact Nat.lt_succ_self _
  have hBlast :
      (T.boundary.map (Blowup.strictTransform π Z) ++ [Blowup.exceptionalIdeal π Z])[T.boundary.length]'hnlt
        = Blowup.exceptionalIdeal π Z := getElem_length_map_strictTransform_append π Z T.boundary hnlt
  have hexists : ∃ t : Fin m, a T.boundary.length = some t := by
    cases hh : a T.boundary.length with
    | none =>
        exfalso
        have h0 := hnone T.boundary.length hnlt hh
        rw [hBlast] at h0
        exact notMem_support_of_restrictIdeal_eq_top (Blowup.exceptionalIdeal π Z) U ξ' hξU h0 hmem
    | some t => exact ⟨t, rfl⟩
  obtain ⟨t₀, hat₀⟩ := hexists
  have hexcU : restrictIdeal (Blowup.exceptionalIdeal π Z) U = c.coordIdeal {t₀} := by
    have h0 := hsome T.boundary.length hnlt t₀ hat₀
    rwa [hBlast] at h0
  have hchoice : ∀ j : Fin T.boundary.length, ∃ t : Fin m,
      j ∈ J → (a (j : ℕ) = some t ∧
        restrictIdeal (Blowup.strictTransform π Z (T.boundary.get j)) U = c.coordIdeal {t}) := by
    intro j
    by_cases hj : j ∈ J
    · have hjlt : (j : ℕ)
          < (T.boundary.map (Blowup.strictTransform π Z) ++ [Blowup.exceptionalIdeal π Z]).length := by
        rw [hlen]; exact Nat.lt_succ_of_lt j.isLt
      have hBj : (T.boundary.map (Blowup.strictTransform π Z)
            ++ [Blowup.exceptionalIdeal π Z])[(j : ℕ)]'hjlt
          = Blowup.strictTransform π Z (T.boundary.get j) := by
        rw [List.get_eq_getElem]
        exact getElem_map_strictTransform_append_of_lt π Z T.boundary (j : ℕ) j.isLt hjlt
      have hmemj : ξ' ∈ (Blowup.strictTransform π Z (T.boundary.get j)).support :=
        (mem_support_intersectionIdeal_transformedBoundary_iff T X' π Z J ξ').mp hξ'A' j hj
      cases hh : a (j : ℕ) with
      | none =>
          exfalso
          have h0 := hnone (j : ℕ) hjlt hh
          rw [hBj] at h0
          exact notMem_support_of_restrictIdeal_eq_top _ U ξ' hξU h0 hmemj
      | some t =>
          refine ⟨t, fun _ => ⟨rfl, ?_⟩⟩
          have h0 := hsome (j : ℕ) hjlt t hh
          rwa [hBj] at h0
    · exact ⟨t₀, fun h => absurd h hj⟩
  choose tfun htfun using hchoice
  have ht₀notin : t₀ ∉ J.image tfun := by
    intro hcon
    obtain ⟨j, hj, hjt⟩ := Finset.mem_image.mp hcon
    have h1 : a (j : ℕ) = some t₀ := by rw [(htfun j hj).1, hjt]
    have hjlt : (j : ℕ)
        < (T.boundary.map (Blowup.strictTransform π Z) ++ [Blowup.exceptionalIdeal π Z]).length := by
      rw [hlen]; exact Nat.lt_succ_of_lt j.isLt
    have h2 := hinj (j : ℕ) hjlt T.boundary.length hnlt t₀ h1 hat₀
    exact absurd h2 (Nat.ne_of_lt j.isLt)
  have hstep1 : restrictIdeal (intersectionIdeal (transformedBoundary π Z T.boundary)
        (J.image (strictTransformIndex π Z T.boundary))) U
      = ⨆ j' ∈ J.image (strictTransformIndex π Z T.boundary),
          restrictIdeal ((transformedBoundary π Z T.boundary).get j') U := by
    rw [intersectionIdeal_eq_iSup]
    exact MonomialChart.restrictIdeal_biSup_finset U
      (fun j' => (transformedBoundary π Z T.boundary).get j') _
  have hstep2 : (⨆ j' ∈ J.image (strictTransformIndex π Z T.boundary),
          restrictIdeal ((transformedBoundary π Z T.boundary).get j') U)
      = ⨆ j ∈ J, restrictIdeal
          ((transformedBoundary π Z T.boundary).get (strictTransformIndex π Z T.boundary j)) U :=
    Finset.iSup_finset_image
  have hstep3 : (⨆ j ∈ J, restrictIdeal
          ((transformedBoundary π Z T.boundary).get (strictTransformIndex π Z T.boundary j)) U)
      = ⨆ j ∈ J, c.coordIdeal {tfun j} := by
    refine iSup_congr fun j => iSup_congr fun hj => ?_
    rw [transformedBoundary_get_strictTransformIndex]
    exact (htfun j hj).2
  have hstep4 : (⨆ j ∈ J, c.coordIdeal {tfun j}) = c.coordIdeal (J.image tfun) := by
    rw [MonomialChart.coordIdeal_eq_biSup_singleton, Finset.iSup_finset_image]
  have hZU : restrictIdeal (intersectionIdeal (transformedBoundary π Z T.boundary)
        (J.image (strictTransformIndex π Z T.boundary))) U = c.coordIdeal (J.image tfun) :=
    hstep1.trans (hstep2.trans (hstep3.trans hstep4))
  obtain ⟨O, hOopen, hOne, hOsub⟩ := exists_isOpen_inter_subset_of_maximal
    ((↑(intersectionIdeal (transformedBoundary π Z T.boundary)
        (J.image (strictTransformIndex π Z T.boundary))).support : Set ↥X'))
    (Scheme.IdealSheafData.support (intersectionIdeal (transformedBoundary π Z T.boundary)
      (J.image (strictTransformIndex π Z T.boundary)))).isClosed C' hC'irr hC'sub hC'max
  have hξ'O : ξ' ∈ O := by
    obtain ⟨y, hyO, hyA⟩ := hOne
    exact (hξ'.mem_open_set_iff hOopen).mpr ⟨y, hOsub ⟨hyO, hyA⟩, hyO⟩
  obtain ⟨V, hξV, hVle⟩ :=
    AlgebraicGeometry.Scheme.exists_affineOpens_mem_le (X := X') (x := ξ')
      (U := U ⊓ ⟨O, hOopen⟩) ⟨hξU, hξ'O⟩
  have hVU : (V : X'.Opens) ≤ U := le_trans hVle inf_le_left
  have hZV : restrictIdeal (intersectionIdeal (transformedBoundary π Z T.boundary)
        (J.image (strictTransformIndex π Z T.boundary))) (V : X'.Opens)
      = (c.restrict hVU).coordIdeal (J.image tfun) :=
    restrictIdeal_eq_restrict_coordIdeal_of_le hVU c _ _ hZU
  have hEV : restrictIdeal (Blowup.exceptionalIdeal π Z) (V : X'.Opens)
      = (c.restrict hVU).coordIdeal {t₀} :=
    restrictIdeal_eq_restrict_coordIdeal_of_le hVU c _ _ hexcU
  refine not_inter_support_subset_support_of_notMem_coordIdeal (π ≫ T.structMap) V.2
    (c.restrict hVU) _ _ (J.image tfun) t₀ ht₀notin hZV hEV ξ' hξV hξ'A' ?_
  rintro x ⟨hxA, hxV⟩
  have hxmem := hVle hxV
  have hxO : x ∈ O := hxmem.2
  have hCE : C' ⊆ (↑(Blowup.exceptionalIdeal π Z).support : Set ↥X') :=
    (hξ'.mem_closed_set_iff
      (Scheme.IdealSheafData.support (Blowup.exceptionalIdeal π Z)).isClosed).mp hmem
  exact hCE (hOsub ⟨hxO, hxA⟩)

theorem intersectionComponents_transformedBoundary_of_isBlowupAlongIdealSheaf :
    ∀ (T : MarkedIdealWithBoundary.{u}), T.IsAdmissible →
      ∀ (J₀ : Finset (Fin T.boundary.length)),
        ∀ 𝒞 ⊆ intersectionComponents T.boundary J₀,
          ∀ (hop : IsOpen (⇑(intersectionIdeal T.boundary J₀).subschemeι ⁻¹' ⋃₀ 𝒞)) (X' : Scheme.{u})
            (π : X' ⟶ T.scheme),
            Blowup.IsBlowupAlongIdealSheaf π (componentUnionIdeal T.boundary J₀ 𝒞 hop) →
              ∀ (J : Finset (Fin T.boundary.length)),
                ∀ C' ∈ intersectionComponents
                      (transformedBoundary π (componentUnionIdeal T.boundary J₀ 𝒞 hop) T.boundary)
                      (Finset.image
                        (strictTransformIndex π (componentUnionIdeal T.boundary J₀ 𝒞 hop) T.boundary) J),
                  ∀ ξ' : ↥X', IsGenericPoint ξ' C' →
                    ξ' ∉ (Blowup.exceptionalIdeal π (componentUnionIdeal T.boundary J₀ 𝒞 hop)).support ∧
                      ∃ C ∈ intersectionComponents T.boundary J,
                        C ∉ 𝒞 ∧
                          C' = closure (⇑π ⁻¹' C \
                              (↑(Blowup.exceptionalIdeal π
                                  (componentUnionIdeal T.boundary J₀ 𝒞 hop)).support : Set ↥X')) ∧
                            ∀ ξ : ↥T.scheme, IsGenericPoint ξ C → π ξ' = ξ := by
  intro T hT J₀ 𝒞 h𝒞 hop X' π hπ J C' hC' ξ' hξ'
  have : IsNoetherian T.scheme := hT.isNoetherian
  have : IsNoetherian X' := isNoetherian_of_isBlowupAlongIdealSheaf hπ
  have : IsLocallyNoetherian X' := inferInstance
  have : NoetherianSpace ↥X' := inferInstance
  obtain ⟨hC'irr, hC'sub, hC'max⟩ := hC'
  have hsncZ : HasStrictNormalCrossingsWith T.structMap (componentUnionIdeal T.boundary J₀ 𝒞 hop) T.boundary :=
    MonomialCenterGeometry.hasStrictNormalCrossingsWith_componentUnionIdeal T hT J₀ 𝒞 h𝒞 hop
  have hξ'E : ξ' ∉ (Blowup.exceptionalIdeal π (componentUnionIdeal T.boundary J₀ 𝒞 hop)).support :=
    genericPoint_notMem_support_exceptionalIdeal T _ hsncZ X' π hπ J C' hC'irr hC'sub hC'max ξ' hξ'
  have hπξ' : π ξ' ∉ (componentUnionIdeal T.boundary J₀ 𝒞 hop).support := by
    intro hcon
    apply hξ'E
    have h0 : ξ' ∈ (↑((componentUnionIdeal T.boundary J₀ 𝒞 hop).comap π).support : Set ↥X') := by
      rw [support_comap_eq]
      exact hcon
    exact h0
  have hξ'A' : ξ' ∈ (intersectionIdeal
      (transformedBoundary π (componentUnionIdeal T.boundary J₀ 𝒞 hop) T.boundary)
      (J.image (strictTransformIndex π (componentUnionIdeal T.boundary J₀ 𝒞 hop) T.boundary))).support :=
    hC'sub hξ'.mem
  have hξA : π ξ' ∈ (intersectionIdeal T.boundary J).support :=
    (mem_support_intersectionIdeal_transformedBoundary_iff_of_notMem π _ T.boundary J ξ' hπξ').mp hξ'A'
  have hAclosed : IsClosed ((intersectionIdeal T.boundary J).support : Set ↥T.scheme) :=
    (Scheme.IdealSheafData.support (intersectionIdeal T.boundary J)).isClosed
  have hCsubA : closure ({π ξ'} : Set ↥T.scheme)
      ⊆ ((intersectionIdeal T.boundary J).support : Set ↥T.scheme) :=
    closure_minimal (Set.singleton_subset_iff.mpr hξA) hAclosed
  have hmax : ∀ D : Set ↥T.scheme, IsIrreducible D → closure ({π ξ'} : Set ↥T.scheme) ⊆ D →
      D ⊆ ((intersectionIdeal T.boundary J).support : Set ↥T.scheme) →
      D = closure ({π ξ'} : Set ↥T.scheme) := by
    intro D hDirr hCsubD hDsubA
    obtain ⟨η, hηspec⟩ : ∃ η : ↥T.scheme, IsGenericPoint η (closure D) :=
      QuasiSober.sober (IsIrreducible.closure hDirr) isClosed_closure
    have hπξ'D : π ξ' ∈ closure D :=
      subset_closure (hCsubD (subset_closure (Set.mem_singleton _)))
    have hηnotZ : η ∉ (componentUnionIdeal T.boundary J₀ 𝒞 hop).support := by
      intro hcon
      apply hπξ'
      have h1 : closure D
          ⊆ (↑(componentUnionIdeal T.boundary J₀ 𝒞 hop).support : Set ↥T.scheme) := by
        rw [← hηspec]
        exact closure_minimal (Set.singleton_subset_iff.mpr hcon)
          (Scheme.IdealSheafData.support (componentUnionIdeal T.boundary J₀ 𝒞 hop)).isClosed
      exact h1 hπξ'D
    have hs : π ξ' ∈ closure ({η} : Set ↥T.scheme) := by
      rw [hηspec]; exact hπξ'D
    obtain ⟨x, hxη, hξ'x⟩ := exists_lift_of_specializes_of_isBlowupAlongIdealSheaf π
      (componentUnionIdeal T.boundary J₀ 𝒞 hop) hπ η hηnotZ ξ' hπξ' hs
    have hxnotZ : π x ∉ (componentUnionIdeal T.boundary J₀ 𝒞 hop).support := by
      rw [hxη]; exact hηnotZ
    have hxA' : x ∈ (intersectionIdeal
        (transformedBoundary π (componentUnionIdeal T.boundary J₀ 𝒞 hop) T.boundary)
        (J.image (strictTransformIndex π (componentUnionIdeal T.boundary J₀ 𝒞 hop) T.boundary))).support := by
      refine (mem_support_intersectionIdeal_transformedBoundary_iff_of_notMem π _ T.boundary J x hxnotZ).mpr ?_
      have h1 : π x ∈ closure D := by
        rw [hxη]; exact hηspec.mem
      exact (closure_minimal hDsubA hAclosed) h1
    have hclxsub : closure ({x} : Set ↥X') ⊆ (↑(intersectionIdeal
        (transformedBoundary π (componentUnionIdeal T.boundary J₀ 𝒞 hop) T.boundary)
        (J.image (strictTransformIndex π (componentUnionIdeal T.boundary J₀ 𝒞 hop) T.boundary))).support
          : Set ↥X') :=
      closure_minimal (Set.singleton_subset_iff.mpr hxA')
        (Scheme.IdealSheafData.support (intersectionIdeal
          (transformedBoundary π (componentUnionIdeal T.boundary J₀ 𝒞 hop) T.boundary)
          (J.image (strictTransformIndex π (componentUnionIdeal T.boundary J₀ 𝒞 hop) T.boundary)))).isClosed
    have hC'sub_x : C' ⊆ closure ({x} : Set ↥X') :=
      (hξ'.mem_closed_set_iff isClosed_closure).mp hξ'x
    have hclx : closure ({x} : Set ↥X') = C' :=
      hC'max _ (IsIrreducible.closure isIrreducible_singleton) hC'sub_x hclxsub
    have hxC' : x ∈ C' := by
      rw [← hclx]; exact subset_closure (Set.mem_singleton x)
    have hxclξ' : x ∈ closure ({ξ'} : Set ↥X') := by
      rw [hξ'.def]
      exact hxC'
    have hπxcl : π x ∈ closure ({π ξ'} : Set ↥T.scheme) := by
      have hsub : closure ({ξ'} : Set ↥X')
          ⊆ ⇑π.base ⁻¹' closure ({π ξ'} : Set ↥T.scheme) := by
        refine closure_minimal (Set.singleton_subset_iff.mpr ?_) ?_
        · exact subset_closure (Set.mem_singleton _)
        · exact isClosed_closure.preimage π.base.hom.continuous
      exact hsub hxclξ'
    refine Set.Subset.antisymm ?_ hCsubD
    have h2 : closure D ⊆ closure ({π ξ'} : Set ↥T.scheme) := by
      rw [← hηspec]
      refine closure_minimal (Set.singleton_subset_iff.mpr ?_) isClosed_closure
      rw [← hxη]; exact hπxcl
    exact fun z hz => h2 (subset_closure hz)
  have hCcomp : closure ({π ξ'} : Set ↥T.scheme) ∈ intersectionComponents T.boundary J :=
    ⟨IsIrreducible.closure isIrreducible_singleton, hCsubA, hmax⟩
  have hCnot : closure ({π ξ'} : Set ↥T.scheme) ∉ 𝒞 := by
    intro hcon
    apply hπξ'
    have h1 : π ξ' ∈ ⋃₀ 𝒞 := ⟨_, hcon, subset_closure (Set.mem_singleton _)⟩
    rw [← componentUnionIdeal_support_eq_sUnion T hT J₀ 𝒞 h𝒞 hop] at h1
    exact h1
  have hCeq : C' = closure ((⇑π ⁻¹' closure ({π ξ'} : Set ↥T.scheme)) \
      (↑(Blowup.exceptionalIdeal π (componentUnionIdeal T.boundary J₀ 𝒞 hop)).support : Set ↥X')) := by
    apply Set.Subset.antisymm
    · rw [← hξ'.def]
      refine closure_mono (Set.singleton_subset_iff.mpr ?_)
      exact ⟨subset_closure (Set.mem_singleton _), hξ'E⟩
    · refine closure_minimal ?_ ?_
      · rintro x ⟨hx1, hx2⟩
        have hxnotZ : π x ∉ (componentUnionIdeal T.boundary J₀ 𝒞 hop).support := by
          intro hcon
          apply hx2
          have h0 : x ∈ (↑((componentUnionIdeal T.boundary J₀ 𝒞 hop).comap π).support
              : Set ↥X') := by
            rw [support_comap_eq]
            exact hcon
          exact h0
        obtain ⟨x₀, hx₀, hxx₀⟩ := exists_lift_of_specializes_of_isBlowupAlongIdealSheaf π
          (componentUnionIdeal T.boundary J₀ 𝒞 hop) hπ (π ξ') hπξ' x hxnotZ hx1
        have hx₀eq : x₀ = ξ' :=
          eq_of_isBlowupAlongIdealSheaf_of_notMem_support π (componentUnionIdeal T.boundary J₀ 𝒞 hop) hπ x₀ ξ'
            (by rw [hx₀]; exact hπξ') hπξ' hx₀
        rw [hx₀eq] at hxx₀
        rw [← hξ'.def]
        exact hxx₀
      · rw [← hξ'.def]
        exact isClosed_closure
  refine ⟨hξ'E, closure ({π ξ'} : Set ↥T.scheme), hCcomp, hCnot, hCeq, ?_⟩
  intro ξ hgen
  have h0 : IsGenericPoint (π ξ') (closure ({π ξ'} : Set ↥T.scheme)) := rfl
  exact IsGenericPoint.eq h0 hgen

end FunctorialResolution.EmbeddedResolution

end
