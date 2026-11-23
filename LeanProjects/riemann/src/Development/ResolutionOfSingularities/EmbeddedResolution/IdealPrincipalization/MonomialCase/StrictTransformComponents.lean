import Mathlib
import Development.ResolutionOfSingularities.Foundations.Blowup.BlowupBasic
import Development.ResolutionOfSingularities.Foundations.Blowup.BlowupIsoOffCenter
import Development.ResolutionOfSingularities.Foundations.Blowup.BlowupProperties
import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.ClopenRestriction
import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.NoetherianBlowup
import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.Saturation
import Development.ResolutionOfSingularities.EmbeddedResolution.IteratedBlowups.StrictTransform
import Development.ResolutionOfSingularities.Foundations.Blowup.StrictTransform
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.StrictNormalCrossings
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.OrderReductionProperties
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MonomialCase.MonomialGeometryHypotheses
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MonomialCase.CenterInvariant
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.IdealBlowupSequence
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.MarkedSequenceOfBlowups
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MarkedBlowupSequence.SupportsAlongSequence
import Development.ResolutionOfSingularities.Foundations.BlowupUniversalProperty
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionOfSingularities
universe u

open CategoryTheory AlgebraicGeometry TopologicalSpace

noncomputable section

namespace FunctorialResolution.EmbeddedResolution

theorem exists_isOpen_inter_subset_of_maximal {α : Type*} [TopologicalSpace α]
    [TopologicalSpace.NoetherianSpace α] (A : Set α) (hA : IsClosed A) (C : Set α)
    (hC : IsIrreducible C) (hCA : C ⊆ A)
    (hmax : ∀ C' : Set α, IsIrreducible C' → C ⊆ C' → C' ⊆ A → C' = C) :
    ∃ O : Set α, IsOpen O ∧ (O ∩ A).Nonempty ∧ O ∩ A ⊆ C := by
  classical
  obtain ⟨S, hirr, hsup⟩ :=
    TopologicalSpace.NoetherianSpace.exists_finset_irreducible
      (⟨A, hA⟩ : TopologicalSpace.Closeds α)
  have hcoe : ∀ S' : Finset (TopologicalSpace.Closeds α),
      ((S'.sup id : TopologicalSpace.Closeds α) : Set α) = ⋃ k ∈ S', (k : Set α) := by
    intro S'
    refine Finset.induction_on S' ?_ ?_
    · simp
    · intro a S'' _ ih
      simp [Finset.sup_insert, ih]
  have hA' : A = ⋃ k ∈ S, (k : Set α) :=
    (congrArg (fun s : TopologicalSpace.Closeds α => (s : Set α)) hsup).trans (hcoe S)
  obtain ⟨T, hTdef⟩ : ∃ T : Finset (TopologicalSpace.Closeds α),
      T = S.filter (fun k : TopologicalSpace.Closeds α => ¬ ((k : Set α) ⊆ C)) := ⟨_, rfl⟩
  have hmemT : ∀ k : TopologicalSpace.Closeds α,
      k ∈ T ↔ k ∈ S ∧ ¬ ((k : Set α) ⊆ C) := by
    intro k
    rw [hTdef]
    exact Finset.mem_filter
  have hTcl : IsClosed (⋃ k ∈ T, (k : Set α)) :=
    Set.Finite.isClosed_biUnion (Finset.finite_toSet _) (fun k _ => k.2)
  refine ⟨(⋃ k ∈ T, (k : Set α))ᶜ, hTcl.isOpen_compl, ?_, ?_⟩
  · by_contra hemp
    have hAsub : A ⊆ ⋃ k ∈ T, (k : Set α) := by
      intro z hz
      by_contra hz'
      exact hemp ⟨z, hz', hz⟩
    obtain ⟨s, hsT, hCs⟩ :=
      isIrreducible_iff_sUnion_isClosed.mp hC
        (T.image fun k : TopologicalSpace.Closeds α => (k : Set α))
        (by
          intro z hz
          obtain ⟨k, -, rfl⟩ := Finset.mem_image.mp hz
          exact k.2)
        (by
          refine hCA.trans (hAsub.trans ?_)
          intro z hz
          obtain ⟨k, hk, hzk⟩ := Set.mem_iUnion₂.mp hz
          exact Set.mem_sUnion.mpr
            ⟨(k : Set α), Finset.mem_coe.mpr (Finset.mem_image_of_mem _ hk), hzk⟩)
    obtain ⟨k, hkT, rfl⟩ := Finset.mem_image.mp hsT
    have hkS : k ∈ S := ((hmemT k).mp hkT).1
    have hkA : (k : Set α) ⊆ A := by
      rw [hA']
      exact fun z hz => Set.mem_iUnion₂.mpr ⟨k, hkS, hz⟩
    exact ((hmemT k).mp hkT).2 (le_of_eq (hmax (k : Set α) (hirr ⟨k, hkS⟩) hCs hkA))
  · rintro z ⟨hzO, hzA⟩
    rw [hA'] at hzA
    obtain ⟨k, hkS, hzk⟩ := Set.mem_iUnion₂.mp hzA
    by_cases hk : (k : Set α) ⊆ C
    · exact hk hzk
    · exact absurd (Set.mem_iUnion₂.mpr ⟨k, (hmemT k).mpr ⟨hkS, hk⟩, hzk⟩) hzO

theorem exists_specializes_of_homeomorph {α β : Type*} [TopologicalSpace α] [TopologicalSpace β]
    (p : α → Prop) (q : β → Prop) (f : α → β) (e : {x : α // p x} ≃ₜ {y : β // q y})
    (he : ∀ x : {x : α // p x}, ((e x : β)) = f (x : α))
    (ξ : β) (hξ : q ξ) (y : α) (hy : p y) (hs : f y ∈ closure ({ξ} : Set β)) :
    ∃ x : α, p x ∧ f x = ξ ∧ y ∈ closure ({x} : Set α) := by
  refine ⟨((e.symm ⟨ξ, hξ⟩ : {x : α // p x}) : α), (e.symm ⟨ξ, hξ⟩).2, ?_, ?_⟩
  · have h1 := he (e.symm ⟨ξ, hξ⟩)
    rw [← h1]
    simp
  · have h2 : ((e ⟨y, hy⟩ : {z : β // q z}) : β) ∈ closure ({ξ} : Set β) := by
      rw [he ⟨y, hy⟩]
      exact hs
    have h3 : (e ⟨y, hy⟩) ∈ closure ({(⟨ξ, hξ⟩ : {z : β // q z})} : Set {z : β // q z}) := by
      rw [closure_subtype, Set.image_singleton]
      exact h2
    have h4 := Set.mem_image_of_mem (⇑e.symm) h3
    rw [e.symm.image_closure, Set.image_singleton, Homeomorph.symm_apply_apply] at h4
    have h5 := closure_subtype.mp h4
    rwa [Set.image_singleton] at h5

theorem exists_lift_of_specializes_of_isBlowupAlongIdealSheaf {X X' : Scheme.{u}} (π : X' ⟶ X)
    (Z : X.IdealSheafData) (h : Blowup.IsBlowupAlongIdealSheaf π Z) (ξ : ↥X) (hξ : ξ ∉ Z.support)
    (y : ↥X') (hy : π y ∉ Z.support) (hs : π y ∈ closure ({ξ} : Set ↥X)) :
    ∃ x : ↥X', π x = ξ ∧ y ∈ closure ({x} : Set ↥X') := by
  have h1 := h.restrict Z.support.compl
  rw [Blowup.comap_ι_support_compl_eq_top Z] at h1
  have hiso : IsIso (π ∣_ Z.support.compl) := h1.isIso_of_top
  obtain ⟨e, he⟩ : ∃ e : {a : ↥X' // a ∈ (π ⁻¹ᵁ Z.support.compl)} ≃ₜ
      {b : ↥X // b ∈ Z.support.compl},
      ∀ a : {a : ↥X' // a ∈ (π ⁻¹ᵁ Z.support.compl)},
        ((e a : ↥X)) = (⇑π.base) (a : ↥X') :=
    ⟨Scheme.homeoOfIso (asIso (π ∣_ Z.support.compl)),
      fun a => morphismRestrict_base_coe π Z.support.compl a⟩
  have hξ' : ξ ∈ Z.support.compl := hξ
  have hy' : y ∈ (π ⁻¹ᵁ Z.support.compl) := hy
  obtain ⟨x, -, hx1, hx2⟩ :=
    exists_specializes_of_homeomorph (fun a : ↥X' => a ∈ (π ⁻¹ᵁ Z.support.compl))
      (fun b : ↥X => b ∈ Z.support.compl) (fun a => (⇑π.base) a) e he ξ hξ' y hy' hs
  exact ⟨x, hx1, hx2⟩

theorem eq_of_isBlowupAlongIdealSheaf_of_notMem_support {X X' : Scheme.{u}} (π : X' ⟶ X)
    (Z : X.IdealSheafData) (h : Blowup.IsBlowupAlongIdealSheaf π Z) (x y : ↥X')
    (hx : π x ∉ Z.support) (hy : π y ∉ Z.support) (hxy : π x = π y) : x = y := by
  have h1 := h.restrict Z.support.compl
  rw [Blowup.comap_ι_support_compl_eq_top Z] at h1
  have hiso : IsIso (π ∣_ Z.support.compl) := h1.isIso_of_top
  obtain ⟨e, he⟩ : ∃ e : {a : ↥X' // a ∈ (π ⁻¹ᵁ Z.support.compl)} ≃ₜ
      {b : ↥X // b ∈ Z.support.compl},
      ∀ a : {a : ↥X' // a ∈ (π ⁻¹ᵁ Z.support.compl)},
        ((e a : ↥X)) = (⇑π.base) (a : ↥X') :=
    ⟨Scheme.homeoOfIso (asIso (π ∣_ Z.support.compl)),
      fun a => morphismRestrict_base_coe π Z.support.compl a⟩
  have hx' : x ∈ (π ⁻¹ᵁ Z.support.compl) := hx
  have hy' : y ∈ (π ⁻¹ᵁ Z.support.compl) := hy
  have key : e ⟨x, hx'⟩ = e ⟨y, hy'⟩ := by
    apply Subtype.ext
    rw [he ⟨x, hx'⟩, he ⟨y, hy'⟩]
    exact hxy
  exact congrArg Subtype.val (e.injective key)

theorem notMem_support_exceptionalIdeal {X X' : Scheme.{u}} (π : X' ⟶ X)
    (Z : X.IdealSheafData) (y : ↥X') (hy : π y ∉ Z.support) :
    y ∉ (Blowup.exceptionalIdeal π Z).support := by
  have h1 : (((Z.comap π).support : TopologicalSpace.Closeds ↥X') : Set ↥X')
      = ⇑π.base ⁻¹' ((Z.support : TopologicalSpace.Closeds ↥X) : Set ↥X) := by
    rw [Scheme.IdealSheafData.support_comap]; rfl
  intro hmem
  have hmem' : y ∈ (((Z.comap π).support : TopologicalSpace.Closeds ↥X') : Set ↥X') := hmem
  rw [h1] at hmem'
  exact hy hmem'

theorem exists_eq_closure_of_isIrreducibleComponentOf_strictTransform :
    ∀ (T : MarkedIdealWithBoundary.{u}), T.IsAdmissible →
      ∀ (Z : T.scheme.IdealSheafData),
        AlgebraicGeometry.Smooth (CategoryTheory.CategoryStruct.comp Z.subschemeι T.structMap) →
        HasStrictNormalCrossingsWith T.structMap Z T.boundary →
        ∀ (X' : Scheme.{u}) (π : X' ⟶ T.scheme), Blowup.IsBlowupAlongIdealSheaf π Z →
          ∀ D ∈ T.boundary,
            ∀ C' : Set ↥X',
              IsIrreducibleComponentOf C' (↑(Blowup.strictTransform π Z D).support : Set ↥X') →
              ∃ (η' : ↥X') (C : Set ↥T.scheme),
                C' = closure ({η'} : Set ↥X') ∧
                η' ∉ (Blowup.exceptionalIdeal π Z).support ∧
                IsIrreducibleComponentOf C (↑D.support : Set ↥T.scheme) ∧
                ¬ C ⊆ (↑Z.support : Set ↥T.scheme) ∧
                C = closure ({π η'} : Set ↥T.scheme) := by
  intro T hT Z _hsm _hsnc X' π hπ D _hD C' hC'
  have hTnoeth : AlgebraicGeometry.IsNoetherian T.scheme := hT.isNoetherian
  have hX'noeth : AlgebraicGeometry.IsNoetherian X' := isNoetherian_of_isBlowupAlongIdealSheaf hπ
  have hX'loc : AlgebraicGeometry.IsLocallyNoetherian X' := inferInstance
  have hX'top : TopologicalSpace.NoetherianSpace ↥X' := inferInstance
  obtain ⟨hC'irr, hC'sub, hC'max⟩ := hC'
  have hcont : Continuous (⇑π.base) := π.continuous
  have hSclosed : IsClosed (↑(Blowup.strictTransform π Z D).support : Set ↥X') :=
    (Blowup.strictTransform π Z D).support.2
  have hSeq : (↑(Blowup.strictTransform π Z D).support : Set ↥X')
      = closure (⇑π.base ⁻¹'
          ((↑D.support : Set ↥T.scheme) \ (↑Z.support : Set ↥T.scheme))) :=
    support_strictTransform_eq_closure_preimage π Z D
  have hC'closed : IsClosed C' := by
    have h1 : closure C' = C' :=
      hC'max (closure C') hC'irr.closure subset_closure
        (hSclosed.closure_subset_iff.mpr hC'sub)
    rw [← h1]
    exact isClosed_closure
  obtain ⟨η', hgen⟩ := QuasiSober.sober hC'irr hC'closed
  have hη'' : closure ({η'} : Set ↥X') = C' := hgen
  obtain ⟨O, hOopen, hOne, hOsub⟩ :=
    exists_isOpen_inter_subset_of_maximal (↑(Blowup.strictTransform π Z D).support : Set ↥X')
      hSclosed C' hC'irr hC'sub hC'max
  obtain ⟨w, hwO, hwS⟩ := hOne
  have hwA : w ∈ closure (⇑π.base ⁻¹'
      ((↑D.support : Set ↥T.scheme) \ (↑Z.support : Set ↥T.scheme))) := by
    rw [← hSeq]; exact hwS
  obtain ⟨a, haO, haA⟩ := mem_closure_iff.mp hwA O hOopen hwO
  have haA' : (⇑π.base) a
      ∈ ((↑D.support : Set ↥T.scheme) \ (↑Z.support : Set ↥T.scheme)) := haA
  have haS : a ∈ (↑(Blowup.strictTransform π Z D).support : Set ↥X') := by
    rw [hSeq]
    exact subset_closure haA
  have haC' : a ∈ C' := hOsub ⟨haO, haS⟩
  have hVopen : IsOpen ((π ⁻¹ᵁ Z.support.compl : X'.Opens) : Set ↥X') :=
    (π ⁻¹ᵁ Z.support.compl).isOpen
  have haV : a ∈ ((π ⁻¹ᵁ Z.support.compl : X'.Opens) : Set ↥X') := haA'.2
  have hη'V : η' ∈ ((π ⁻¹ᵁ Z.support.compl : X'.Opens) : Set ↥X') := by
    have h1 : a ∈ closure ({η'} : Set ↥X') := by rw [hη'']; exact haC'
    obtain ⟨z, hzV, hz⟩ := mem_closure_iff.mp h1 _ hVopen haV
    have hz' : z = η' := hz
    rwa [hz'] at hzV
  have hπη' : (⇑π.base) η' ∉ (↑Z.support : Set ↥T.scheme) := hη'V
  have hη'S : η' ∈ (↑(Blowup.strictTransform π Z D).support : Set ↥X') := by
    refine hC'sub ?_
    rw [← hη'']
    exact subset_closure rfl
  have hπη'D : (⇑π.base) η' ∈ (↑D.support : Set ↥T.scheme) := by
    have h2 : η' ∈ closure (⇑π.base ⁻¹'
        ((↑D.support : Set ↥T.scheme) \ (↑Z.support : Set ↥T.scheme))) := by
      rw [← hSeq]; exact hη'S
    have h3 : closure (⇑π.base ⁻¹'
          ((↑D.support : Set ↥T.scheme) \ (↑Z.support : Set ↥T.scheme)))
        ⊆ ⇑π.base ⁻¹' (↑D.support : Set ↥T.scheme) :=
      closure_minimal (Set.preimage_mono Set.sdiff_subset)
        (IsClosed.preimage hcont D.support.2)
    exact h3 h2
  have hCirr : IsIrreducible (closure ({((⇑π.base) η')} : Set ↥T.scheme)) :=
    isIrreducible_singleton.closure
  have hCsub : closure ({((⇑π.base) η')} : Set ↥T.scheme) ⊆ (↑D.support : Set ↥T.scheme) :=
    closure_minimal (Set.singleton_subset_iff.mpr hπη'D) D.support.2
  have hCmax : ∀ C₂ : Set ↥T.scheme, IsIrreducible C₂ →
      closure ({((⇑π.base) η')} : Set ↥T.scheme) ⊆ C₂ →
      C₂ ⊆ (↑D.support : Set ↥T.scheme) →
      C₂ = closure ({((⇑π.base) η')} : Set ↥T.scheme) := by
    intro C₂ hC₂irr hCC₂ hC₂D
    obtain ⟨ξ, hgen2⟩ := QuasiSober.sober hC₂irr.closure isClosed_closure
    have hξ2 : closure ({ξ} : Set ↥T.scheme) = closure C₂ := hgen2
    have hξD : ξ ∈ (↑D.support : Set ↥T.scheme) := by
      have h4 : ξ ∈ closure C₂ := by rw [← hξ2]; exact subset_closure rfl
      exact (closure_minimal hC₂D D.support.2) h4
    have hspec : (⇑π.base) η' ∈ closure ({ξ} : Set ↥T.scheme) := by
      rw [hξ2]
      exact subset_closure (hCC₂ (subset_closure rfl))
    have hξZ : ξ ∉ (↑Z.support : Set ↥T.scheme) := by
      intro hmem
      exact hπη' ((closure_minimal (Set.singleton_subset_iff.mpr hmem) Z.support.2) hspec)
    obtain ⟨x, hx1, hx2⟩ :=
      exists_lift_of_specializes_of_isBlowupAlongIdealSheaf π Z hπ ξ hξZ η' hπη' hspec
    have hx1' : (⇑π.base) x = ξ := hx1
    have hxmem : (⇑π.base) x
        ∈ ((↑D.support : Set ↥T.scheme) \ (↑Z.support : Set ↥T.scheme)) := by
      rw [hx1']
      exact ⟨hξD, hξZ⟩
    have hxS : x ∈ (↑(Blowup.strictTransform π Z D).support : Set ↥X') := by
      rw [hSeq]
      exact subset_closure hxmem
    have hclx : closure ({x} : Set ↥X') ⊆ (↑(Blowup.strictTransform π Z D).support : Set ↥X') :=
      closure_minimal (Set.singleton_subset_iff.mpr hxS) hSclosed
    have hsub2 : C' ⊆ closure ({x} : Set ↥X') := by
      rw [← hη'']
      exact closure_minimal (Set.singleton_subset_iff.mpr hx2) isClosed_closure
    have heq : closure ({x} : Set ↥X') = C' :=
      hC'max (closure ({x} : Set ↥X')) isIrreducible_singleton.closure hsub2 hclx
    have hxC' : x ∈ closure ({η'} : Set ↥X') := by
      rw [hη'', ← heq]
      exact subset_closure rfl
    have himg : (⇑π.base) x ∈ closure (⇑π.base '' ({η'} : Set ↥X')) :=
      image_closure_subset_closure_image hcont ⟨x, hxC', rfl⟩
    rw [Set.image_singleton] at himg
    have hξC : ξ ∈ closure ({((⇑π.base) η')} : Set ↥T.scheme) := by
      rw [← hx1']; exact himg
    refine Set.Subset.antisymm ?_ hCC₂
    refine subset_trans subset_closure ?_
    rw [← hξ2]
    exact closure_minimal (Set.singleton_subset_iff.mpr hξC) isClosed_closure
  have hcomp : IsIrreducibleComponentOf (closure ({((⇑π.base) η')} : Set ↥T.scheme))
      (↑D.support : Set ↥T.scheme) := ⟨hCirr, hCsub, hCmax⟩
  refine ⟨η', closure ({((⇑π.base) η')} : Set ↥T.scheme), hη''.symm,
    notMem_support_exceptionalIdeal π Z η' hπη', hcomp, ?_, rfl⟩
  intro hsub
  exact hπη' (hsub (subset_closure rfl))

end FunctorialResolution.EmbeddedResolution

end
