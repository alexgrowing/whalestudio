import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigidSys
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Splits
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GtBaseChangeSt
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise

namespace GlobalTheory

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField in
open scoped CategoryTheory.Obj TensorProduct Pointwise in

theorem _root_.GlobalTheory.isDominant_pullback_fst_of_isOpenMap {X U Y : Scheme.{0}} (j : U ⟶ X) [IsDominant j]
    (p : Y ⟶ X) (hp : IsOpenMap p) : IsDominant (pullback.fst p j) := by
  rw [isDominant_iff, DenseRange, Scheme.Pullback.range_fst]
  exact j.denseRange.preimage hp

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField in
open scoped CategoryTheory.Obj TensorProduct Pointwise in

theorem _root_.GlobalTheory.eq_of_specializes_of_mem_genericPoints {T : Type*} [TopologicalSpace T] [T0Space T]
    {x y : T} (hx : x ∈ genericPoints T) (h : y ⤳ x) : y = x := by
  have h1 : closure ({y} : Set T) ⊆ closure {x} :=
    hx.2 isIrreducible_singleton.closure h.closure_subset
  exact (h.antisymm (specializes_iff_closure_subset.2 h1)).eq

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField in
open scoped CategoryTheory.Obj TensorProduct Pointwise in

theorem _root_.GlobalTheory.genericPoints_subset_range_of_isDominant {X U : Scheme.{0}} (j : U ⟶ X) [IsDominant j]
    [QuasiCompact j] : genericPoints X ⊆ Set.range j := by
  intro ξ hξ
  obtain ⟨V, hV, hξV, -⟩ := (TopologicalSpace.Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens)
    (show ξ ∈ (⊤ : X.Opens) from trivial)
  replace hV : IsAffineOpen V := hV
  have hc : IsCompact (j ⁻¹' (V : Set X)) :=
    QuasiCompact.isCompact_preimage _ V.isOpen hV.isCompact
  obtain ⟨s, hs, hW⟩ := isCompact_and_isOpen_iff_finite_and_eq_biUnion_affineOpens.mp
    ⟨hc, V.isOpen.preimage j.continuous⟩
  have hcl : ξ ∈ closure (j '' (j ⁻¹' (V : Set X))) := by
    rw [Set.image_preimage_eq_inter_range]
    exact j.denseRange.open_subset_closure_inter V.isOpen hξV
  rw [hW, Set.image_iUnion₂, hs.closure_biUnion, Set.mem_iUnion₂] at hcl
  obtain ⟨W, hWs, hξW⟩ := hcl
  have hWV : (W : Set U) ⊆ j ⁻¹' (V : Set X) := by
    rw [hW]
    exact Set.subset_biUnion_of_mem (u := fun i : U.affineOpens => ((i : U.Opens) : Set U)) hWs
  have hWa : IsAffineOpen (W : U.Opens) := W.2
  set g := hWa.fromSpec ≫ j with hg
  have hrg : Set.range g = j '' (W : Set U) := by
    rw [hg, Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp, hWa.range_fromSpec]
  have hsub : Set.range g ⊆ Set.range hV.fromSpec := by
    rw [hrg, hV.range_fromSpec]
    rintro _ ⟨x, hx, rfl⟩
    exact hWV hx
  set k := IsOpenImmersion.lift hV.fromSpec g hsub with hk
  have hkg : k ≫ hV.fromSpec = g := IsOpenImmersion.lift_fac _ _ _
  set φ := Spec.preimage k
  have hφ : Spec.map φ = k := Spec.map_preimage k
  obtain ⟨p, hp⟩ : ξ ∈ Set.range hV.fromSpec := by rw [hV.range_fromSpec]; exact hξV
  have hinj : Function.Injective hV.fromSpec := hV.fromSpec.isOpenEmbedding.injective
  have hpcl₀ : p ∈ closure (Set.range (Spec.map φ)) := by
    rw [hV.fromSpec.isOpenEmbedding.isInducing.closure_eq_preimage_closure_image,
      Set.mem_preimage, hp]
    convert hξW using 2
    rw [← hrg, ← hkg, ← hφ, Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp]
  have hpcl₁ : (p : PrimeSpectrum Γ(X, V)) ∈ closure (Set.range (PrimeSpectrum.comap φ.hom)) :=
    hpcl₀
  rw [PrimeSpectrum.closure_range_comap] at hpcl₁
  have hpcl : RingHom.ker φ.hom ≤ p.asIdeal := (PrimeSpectrum.mem_zeroLocus _ _).1 hpcl₁
  have hmin : p.asIdeal ∈ (Ideal.comap φ.hom ⊥).minimalPrimes := by
    rw [← RingHom.ker_eq_comap_bot]
    refine ⟨⟨p.2, hpcl⟩, fun q hq hqp => ?_⟩
    have hspec : (⟨q, hq.1⟩ : PrimeSpectrum _) ⤳ p :=
      (PrimeSpectrum.le_iff_specializes _ _).1 hqp
    have heq := _root_.GlobalTheory.eq_of_specializes_of_mem_genericPoints (hp ▸ hξ)
      (hspec.map hV.fromSpec.continuous)
    have heq' := hinj heq
    rw [← heq']
  obtain ⟨q, hq, -, hqp⟩ := Ideal.exists_comap_eq_of_mem_minimalPrimes φ.hom _ hmin
  refine ⟨hWa.fromSpec ⟨q, hq⟩, ?_⟩
  rw [← hp]
  change g ⟨q, hq⟩ = _
  have hgq : g ⟨q, hq⟩ = hV.fromSpec (Spec.map φ ⟨q, hq⟩) := by rw [← hkg, ← hφ]; rfl
  rw [hgq]
  congr 1
  exact PrimeSpectrum.ext hqp

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField in
open scoped CategoryTheory.Obj TensorProduct Pointwise in

theorem _root_.GlobalTheory.isIso_stalkMap_of_flat_of_surjectiveOnStalks {X U : Scheme.{0}} (j : U ⟶ X) [Flat j]
    [SurjectiveOnStalks j] (u : U) : IsIso (j.stalkMap u) := by
  have hs := j.stalkMap_surjective u
  letI := (j.stalkMap u).hom.toAlgebra
  haveI : Module.Flat _ _ := Flat.stalkMap j u
  haveI : IsLocalHom (algebraMap (X.presheaf.stalk (j u)) (U.presheaf.stalk u)) :=
    inferInstanceAs (IsLocalHom (j.stalkMap u).hom)
  haveI := Module.FaithfullyFlat.of_flat_of_isLocalHom
    (A := X.presheaf.stalk (j u)) (B := U.presheaf.stalk u)
  have hi : Function.Injective (j.stalkMap u).hom :=
    FaithfulSMul.algebraMap_injective (X.presheaf.stalk (j u)) (U.presheaf.stalk u)
  exact (ConcreteCategory.isIso_iff_bijective _).2 ⟨hi, hs⟩

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField in
open scoped CategoryTheory.Obj TensorProduct Pointwise in

theorem _root_.GlobalTheory.densePart_basic : ∀ (X U : Scheme.{0}) (j : U ⟶ X), IsPreimmersion j → Flat j → IsDominant j → QuasiCompact j → genericPoints X ⊆ Set.range j ∧ (∀ u : U, IsIso (j.stalkMap u)) ∧ (IsReduced X → IsSchemeTheoreticallyDominant j) ∧ ∀ (Y : Scheme.{0}) (p : Y ⟶ X), UniversallyOpen p → IsDominant (pullback.fst p j) := by
  intro X U j _ _ _ _
  refine ⟨_root_.GlobalTheory.genericPoints_subset_range_of_isDominant j,
    fun u => _root_.GlobalTheory.isIso_stalkMap_of_flat_of_surjectiveOnStalks j u,
    fun _ => (isSchemeTheoreticallyDominant_iff_isDominant j).2 inferInstance,
    fun Y p _ => _root_.GlobalTheory.isDominant_pullback_fst_of_isOpenMap j p p.isOpenMap⟩

end GlobalTheory
