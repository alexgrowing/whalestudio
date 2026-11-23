import Mathlib
import Development.ResolutionOfSingularities.EmbeddedResolution.StrictTransformCharts.CoordinateSubstitution
import Development.ResolutionOfSingularities.EmbeddedResolution.StrictTransformCharts.ControlledTransform
import Development.ResolutionOfSingularities.EmbeddedResolution.DerivativeIdeal.IrreducibleComponentsOfSupport
import Development.ResolutionOfSingularities.Foundations.Schemes.IdealSheafData
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MonomialCase.MonomialPartAlongDivisor
import Development.ResolutionOfSingularities.EmbeddedResolution.IdealPrincipalization.MonomialCase.MonomialSplitting
open AlgebraicGeometry CategoryTheory

universe u

namespace FunctorialResolution.EmbeddedResolution

variable {X Y : Scheme.{u}}

private theorem comap_finset_prod {ι : Type*} (s : Finset ι) (F : ι → X.IdealSheafData)
    (h : Y ⟶ X) : (∏ i ∈ s, F i).comap h = ∏ i ∈ s, (F i).comap h := by
  induction s using Finset.cons_induction with
  | empty => simp
  | cons a s ha ih =>
      rw [Finset.prod_cons, Finset.prod_cons, Scheme.IdealSheafData.comap_mul, ih]

theorem comap_comap_ι (h : Y ⟶ X) (J : X.IdealSheafData) (U : X.Opens) :
    (J.comap h).comap (h ⁻¹ᵁ U).ι = (J.comap U.ι).comap (h ∣_ U) := by
  rw [← Scheme.IdealSheafData.comap_comp, ← Scheme.IdealSheafData.comap_comp, morphismRestrict_ι]

theorem support_comap_subset_biUnion (h : Y ⟶ X) (E : List X.IdealSheafData)
    (M : X.IdealSheafData) (hM : (M.support : Set X) ⊆ ⋃ D ∈ E, (D.support : Set X)) :
    ((M.comap h).support : Set Y) ⊆
      ⋃ D ∈ E.map (fun D : X.IdealSheafData => D.comap h), (D.support : Set Y) := by
  intro y hy
  have hy' : h.base y ∈ (M.support : Set X) := Scheme.IdealSheafData.mem_support_comap.mp hy
  obtain ⟨D, hD, hyD⟩ := Set.mem_iUnion₂.mp (hM hy')
  refine Set.mem_iUnion₂.mpr ⟨D.comap h, List.mem_map.mpr ⟨D, hD, rfl⟩, ?_⟩
  exact Scheme.IdealSheafData.mem_support_comap.mpr hyD

theorem IsMonomialIn.comap_of_isMonomialIn {E : List X.IdealSheafData} {M : X.IdealSheafData}
    (hM : IsMonomialIn E M) (h : Y ⟶ X) :
    IsMonomialIn (E.map (fun D : X.IdealSheafData => D.comap h)) (M.comap h) := by
  intro y
  obtain ⟨U, hU, a, ha⟩ := hM (h.base y)
  have hlen : (E.map (fun D : X.IdealSheafData => D.comap h)).length = E.length := by simp
  refine ⟨h ⁻¹ᵁ U, hU, fun i => a (Fin.cast hlen i), ?_⟩
  have hget : ∀ i : Fin (E.map (fun D : X.IdealSheafData => D.comap h)).length,
      (E.map (fun D : X.IdealSheafData => D.comap h)).get i
        = (E.get (Fin.cast hlen i)).comap h := by
    intro i
    simp [List.get_eq_getElem]
  have hterm : ∀ i : Fin E.length,
      (((E.get i).comap U.ι) ^ a i).comap (h ∣_ U)
        = ((E.get i).comap h).comap (h ⁻¹ᵁ U).ι ^ a i := by
    intro i
    rw [Scheme.IdealSheafData.comap_pow, ← comap_comap_ι h (E.get i) U]
  have hprod : (∏ i : Fin E.length, (((E.get i).comap U.ι) ^ a i).comap (h ∣_ U))
      = ∏ i : Fin E.length, ((E.get i).comap h).comap (h ⁻¹ᵁ U).ι ^ a i :=
    Finset.prod_congr rfl (fun i _ => hterm i)
  rw [comap_comap_ι h M U, ha, comap_finset_prod, hprod,
    ← Fin.prod_congr'
      (fun j : Fin E.length => ((E.get j).comap h).comap (h ⁻¹ᵁ U).ι ^ a j) hlen]
  refine Finset.prod_congr rfl ?_
  intro i _
  rw [hget i]

theorem irreducibleComponents_not_subset_support_comap (h : Y ⟶ X) (hg : GeneralizingMap (fun y : Y => h.base y))
    (E : List X.IdealSheafData) (N : X.IdealSheafData)
    (hN : ∀ D ∈ E, ∀ C : Set X, IsIrreducible C → C ⊆ (D.support : Set X) →
      (∀ C' : Set X, IsIrreducible C' → C' ⊆ (D.support : Set X) → C ⊆ C' → C' ⊆ C) →
      ¬ C ⊆ (N.support : Set X)) :
    ∀ D ∈ E.map (fun D : X.IdealSheafData => D.comap h), ∀ C : Set Y, IsIrreducible C →
      C ⊆ (D.support : Set Y) →
      (∀ C' : Set Y, IsIrreducible C' → C' ⊆ (D.support : Set Y) → C ⊆ C' → C' ⊆ C) →
      ¬ C ⊆ ((N.comap h).support : Set Y) := by
  rintro D' hD' C hC hCsub hCmax hCN
  obtain ⟨D, hD, hDD⟩ := List.mem_map.mp hD'
  have hDD' : D' = D.comap h := hDD.symm
  subst hDD'
  have hCclosed : IsClosed C := by
    rw [← closure_subset_iff_isClosed]
    exact hCmax (closure C) hC.closure
      (closure_minimal hCsub (D.comap h).support.isClosed) subset_closure
  obtain ⟨ξ, hξ⟩ := QuasiSober.sober hC hCclosed
  have hξC : ξ ∈ C := by
    rw [← hξ]
    exact subset_closure (Set.mem_singleton ξ)
  have hxD : h.base ξ ∈ (D.support : Set X) :=
    Scheme.IdealSheafData.mem_support_comap.mp (hCsub hξC)
  have hxN : h.base ξ ∈ (N.support : Set X) :=
    Scheme.IdealSheafData.mem_support_comap.mp (hCN hξC)
  refine hN D hD (closure ({h.base ξ} : Set X)) isIrreducible_singleton.closure
    (closure_minimal (Set.singleton_subset_iff.mpr hxD) D.support.isClosed) ?_
    (closure_minimal (Set.singleton_subset_iff.mpr hxN) N.support.isClosed)
  intro C'' hC'' hC''sub hsub
  obtain ⟨η, hη⟩ := QuasiSober.sober hC''.closure isClosed_closure
  have hηmem : η ∈ closure C'' := by
    rw [← hη]
    exact subset_closure (Set.mem_singleton η)
  have hηD : η ∈ (D.support : Set X) :=
    closure_minimal hC''sub D.support.isClosed hηmem
  have hηspec : η ⤳ h.base ξ := by
    refine specializes_iff_mem_closure.mpr ?_
    rw [hη]
    exact subset_closure (hsub (subset_closure (Set.mem_singleton _)))
  obtain ⟨ξ', hξ'1, hξ'2⟩ := hg hηspec
  have hξ'2' : h.base ξ' = η := hξ'2
  have hξ'D : ξ' ∈ ((D.comap h).support : Set Y) := by
    refine Scheme.IdealSheafData.mem_support_comap.mpr ?_
    rw [hξ'2']
    exact hηD
  have hclos : closure ({ξ'} : Set Y) ⊆ ((D.comap h).support : Set Y) :=
    closure_minimal (Set.singleton_subset_iff.mpr hξ'D) (D.comap h).support.isClosed
  have hCsubξ' : C ⊆ closure ({ξ'} : Set Y) := by
    rw [← hξ]
    exact closure_minimal
      (Set.singleton_subset_iff.mpr (specializes_iff_mem_closure.mp hξ'1)) isClosed_closure
  have hclosure : closure ({ξ'} : Set Y) ⊆ C :=
    hCmax (closure ({ξ'} : Set Y)) isIrreducible_singleton.closure hclos hCsubξ'
  have hξ'C : ξ' ∈ C := hclosure (subset_closure (Set.mem_singleton _))
  have hspec : ξ ⤳ ξ' := by
    refine specializes_iff_mem_closure.mpr ?_
    rw [hξ]
    exact hξ'C
  have hspec2 : h.base ξ ⤳ h.base ξ' := hspec.map h.continuous
  have hηclos : η ∈ closure ({h.base ξ} : Set X) := by
    rw [← hξ'2']
    exact specializes_iff_mem_closure.mp hspec2
  intro z hz
  have hzc : z ∈ closure C'' := subset_closure hz
  rw [← hη] at hzc
  exact closure_minimal (Set.singleton_subset_iff.mpr hηclos) isClosed_closure hzc

theorem isMonomialSplitting_comap_of_generalizingMap (h : Y ⟶ X)
    (hg : GeneralizingMap (fun y : Y => h.base y)) {E : List X.IdealSheafData}
    {I M N : X.IdealSheafData} (hs : IsMonomialSplitting E I M N) :
    IsMonomialSplitting (E.map (fun D : X.IdealSheafData => D.comap h)) (I.comap h) (M.comap h)
      (N.comap h) where
  eq_mul := by rw [hs.eq_mul, Scheme.IdealSheafData.comap_mul]
  monomial_support := support_comap_subset_biUnion h E M hs.monomial_support
  monomial := hs.monomial.comap_of_isMonomialIn h
  transversal := irreducibleComponents_not_subset_support_comap h hg E N hs.transversal

theorem generalizingMap_base_of_flat (h : Y ⟶ X) [AlgebraicGeometry.Flat h] :
    GeneralizingMap (fun y : Y => h.base y) :=
  AlgebraicGeometry.Flat.generalizingMap h

theorem isMonomialSplitting_comap_of_flat (h : Y ⟶ X) [AlgebraicGeometry.Flat h]
    {E : List X.IdealSheafData} {I M N : X.IdealSheafData} (hs : IsMonomialSplitting E I M N) :
    IsMonomialSplitting (E.map (fun D : X.IdealSheafData => D.comap h)) (I.comap h) (M.comap h)
      (N.comap h) :=
  isMonomialSplitting_comap_of_generalizingMap h (generalizingMap_base_of_flat h) hs

theorem isMonomialSplitting_comap_of_smooth (h : Y ⟶ X) [AlgebraicGeometry.Smooth h]
    {E : List X.IdealSheafData} {I M N : X.IdealSheafData} (hs : IsMonomialSplitting E I M N) :
    IsMonomialSplitting (E.map (fun D : X.IdealSheafData => D.comap h)) (I.comap h) (M.comap h)
      (N.comap h) := by
  have : AlgebraicGeometry.Flat h := inferInstance
  exact isMonomialSplitting_comap_of_flat h hs

end FunctorialResolution.EmbeddedResolution
