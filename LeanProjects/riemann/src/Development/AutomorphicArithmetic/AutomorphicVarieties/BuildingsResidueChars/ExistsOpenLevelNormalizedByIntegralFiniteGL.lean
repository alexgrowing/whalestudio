import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.FormsFiniteness.OrderedCechToCatCochainsOneApplyValueAtSubset
import Mathlib.Topology.Algebra.Group.ClosedSubgroup
import Mathlib.Topology.Algebra.OpenSubgroup

open NumberField NumberField.mixedEmbedding Matrix MeasureTheory GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm UpperTheory.V.Af.Fin
open scoped TensorProduct
attribute [local instance 100] LieRing.ofAssociativeRing

private theorem exists_normal_open_level_subgroup {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    (H L : Subgroup G) (hHc : IsCompact (H : Set G)) (hHo : IsOpen (H : Set G))
    (hL : IsOpen (L : Set G)) :
    ∃ L' : Subgroup G, IsOpen (L' : Set G) ∧ L' ≤ L ∧ (∀ k ∈ H, ∀ u ∈ L', k⁻¹ * u * k ∈ L') ∧
      ∃ t : Finset G, ∀ k ∈ H, ∃ c ∈ t, c⁻¹ * k ∈ L' := by
  classical
  haveI : CompactSpace H := isCompact_iff_compactSpace.1 hHc
  have hNo : IsOpen ((L.subgroupOf H : Subgroup H) : Set H) := hL.preimage continuous_subtype_val
  haveI : Finite (H ⧸ L.subgroupOf H) := (L.subgroupOf H).quotient_finite_of_isOpen hNo
  haveI : (L.subgroupOf H).FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
  have hCo : IsOpen ((L.subgroupOf H).normalCore : Set H) :=
    Subgroup.isOpen_of_isClosed_of_finiteIndex _
      ((L.subgroupOf H).normalCore_isClosed (Subgroup.isClosed_of_isOpen _ hNo))
  refine ⟨(L.subgroupOf H).normalCore.map H.subtype, ?_, ?_, ?_, ?_⟩
  · rw [Subgroup.coe_map]
    exact hHo.isOpenMap_subtype_val _ hCo
  · rintro _ ⟨u, hu, rfl⟩
    have := (L.subgroupOf H).normalCore_le hu
    exact this
  · rintro k hk _ ⟨u, hu, rfl⟩
    refine ⟨(⟨k, hk⟩ : H)⁻¹ * u * ⟨k, hk⟩, ?_, by simp⟩
    have := (Subgroup.normalCore_normal (L.subgroupOf H)).conj_mem u hu ((⟨k, hk⟩ : H)⁻¹)
    simpa using this
  · haveI : Finite (H ⧸ (L.subgroupOf H).normalCore) := Subgroup.finite_quotient_of_finiteIndex
    letI := Fintype.ofFinite (H ⧸ (L.subgroupOf H).normalCore)
    refine ⟨Finset.univ.image (fun q : H ⧸ (L.subgroupOf H).normalCore => ((q.out : H) : G)), ?_⟩
    intro k hk
    refine ⟨(((QuotientGroup.mk ⟨k, hk⟩ : H ⧸ (L.subgroupOf H).normalCore).out : H) : G),
      Finset.mem_image_of_mem _ (Finset.mem_univ _), ?_⟩
    have := QuotientGroup.eq.1
      (QuotientGroup.out_eq' (QuotientGroup.mk ⟨k, hk⟩ : H ⧸ (L.subgroupOf H).normalCore))
    exact ⟨_, this, by simp⟩

theorem UpperTheory.exists_open_level_normalized_by_integralFiniteGL :
    ∀ (K : Type) [Field K] [NumberField K] (n : ℕ) (L : Subgroup (AdelicGLn.FiniteAdelicGL K n)), IsOpen (L : Set (AdelicGLn.FiniteAdelicGL K n)) → ∃ L' : Subgroup (AdelicGLn.FiniteAdelicGL K n), IsOpen (L' : Set (AdelicGLn.FiniteAdelicGL K n)) ∧ L' ≤ L ∧ (∀ k ∈ AdelicGLn.integralFiniteGL K n, ∀ u ∈ L', k⁻¹ * u * k ∈ L') ∧ ∃ t : Finset (AdelicGLn.FiniteAdelicGL K n), ∀ k ∈ AdelicGLn.integralFiniteGL K n, ∃ c ∈ t, c⁻¹ * k ∈ L' := by
  intro K _ _ n L hL
  exact exists_normal_open_level_subgroup _ L (AdelicGLn.isCompact_integralFiniteGL K n)
    (AdelicGLn.isOpen_integralFiniteGL K n) hL
