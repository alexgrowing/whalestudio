import Mathlib
import GroundTheory.Brauer.AbsoluteGalois
import GroundTheory.Brauer.BaseChangeCentralizer
import GroundTheory.ProfiniteCohomology.CohomologyFunctoriality
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Brauer

open CategoryTheory groupCohomology GroundTheory.ProfCoh

universe u

section Cocycles

variable {k : Type u} [CommRing k] {H : Type u} [Group H] [TopologicalSpace H]
  [IsTopologicalGroup H] {B : Rep.{u} k H} [IsDiscreteRep B]

theorem homologyMap_H2π {G : Type u} [Group G] {A : Rep.{u} k G}
    (F : inhomogeneousCochains A ⟶ cochainsComplex B) (c : cocycles₂ A) :
    (HomologicalComplex.homologyMap F 2).hom (H2π A c) =
      (cohomologyπ B 2).hom ((HomologicalComplex.cyclesMap F 2).hom ((isoCocycles₂ A).inv.hom c)) := by
  exact congrArg (fun φ => φ.hom ((isoCocycles₂ A).inv.hom c))
    (HomologicalComplex.homologyπ_naturality F 2)

theorem homologyMap_H2π_eq {G₁ G₂ : Type u} [Group G₁] [Group G₂] {A₁ : Rep.{u} k G₁}
    {A₂ : Rep.{u} k G₂} (F₁ : inhomogeneousCochains A₁ ⟶ cochainsComplex B)
    (F₂ : inhomogeneousCochains A₂ ⟶ cochainsComplex B) (c₁ : cocycles₂ A₁) (c₂ : cocycles₂ A₂)
    (h : ((cochainsComplexι B).f 2).hom ((F₁.f 2).hom ((cochainsIso₂ A₁).inv.hom c₁)) =
      ((cochainsComplexι B).f 2).hom ((F₂.f 2).hom ((cochainsIso₂ A₂).inv.hom c₂))) :
    (HomologicalComplex.homologyMap F₁ 2).hom (H2π A₁ c₁) =
      (HomologicalComplex.homologyMap F₂ 2).hom (H2π A₂ c₂) := by
  rw [homologyMap_H2π, homologyMap_H2π]
  congr 1
  apply (ModuleCat.mono_iff_injective ((cochainsComplex B).iCycles 2)).1 inferInstance
  have hi : ∀ {G : Type u} [Group G] {A : Rep.{u} k G}
      (F : inhomogeneousCochains A ⟶ cochainsComplex B) (c : cocycles₂ A),
      ((cochainsComplex B).iCycles 2).hom ((HomologicalComplex.cyclesMap F 2).hom
        ((isoCocycles₂ A).inv.hom c)) = (F.f 2).hom ((cochainsIso₂ A).inv.hom c) := by
    intro G _ A F c
    change ((HomologicalComplex.cyclesMap F 2 ≫ (cochainsComplex B).iCycles 2).hom
      ((isoCocycles₂ A).inv.hom c)) = _
    rw [HomologicalComplex.cyclesMap_i]
    change (F.f 2).hom ((((isoCocycles₂ A).inv ≫ iCocycles A 2)).hom c) = _
    rw [isoCocycles₂_inv_comp_iCocycles]
    rfl
  rw [hi, hi]
  exact (ModuleCat.mono_iff_injective ((cochainsComplexι B).f 2)).1 inferInstance h

end Cocycles

section Topology

variable {K Ks : Type u} [Field K] [Field Ks] [Algebra K Ks]

theorem continuous_restrictScalarsHom (E : IntermediateField K Ks) :
    Continuous (AlgEquiv.restrictScalarsHom K : (Ks ≃ₐ[E] Ks) →* (Ks ≃ₐ[K] Ks)) := by
  refine continuous_of_continuousAt_one _ ?_
  rw [ContinuousAt, map_one]
  intro s hs
  obtain ⟨S, hS, hSs⟩ := (krullTopology_mem_nhds_one_iff K Ks s).1 hs
  rw [Filter.mem_map, krullTopology_mem_nhds_one_iff]
  let b := Module.finBasis K S
  let T : Set Ks := Set.range fun i => (b i : Ks)
  refine ⟨IntermediateField.adjoin E T, ?_, ?_⟩
  · refine IntermediateField.finiteDimensional_adjoin fun x hx => ?_
    obtain ⟨i, rfl⟩ := hx
    exact ((IsIntegral.of_finite K (b i)).map S.val).tower_top
  · intro σ hσ
    apply hSs
    rw [SetLike.mem_coe, IntermediateField.mem_fixingSubgroup_iff] at hσ ⊢
    intro x hx
    have hT : ∀ i, (AlgEquiv.restrictScalarsHom K σ) (b i : Ks) = b i := fun i =>
      hσ _ (IntermediateField.subset_adjoin E T ⟨i, rfl⟩)
    have hx' : x = ∑ i, (b.repr ⟨x, hx⟩ i) • (b i : Ks) := by
      calc x = S.val (∑ i, b.repr ⟨x, hx⟩ i • b i) := by rw [b.sum_repr]; rfl
        _ = ∑ i, (b.repr ⟨x, hx⟩ i) • (b i : Ks) := by
          rw [map_sum]
          exact Finset.sum_congr rfl fun i _ => map_smul S.val _ _
    rw [hx', map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul, hT]

def galUnitsRestrictScalars (E : IntermediateField K Ks) :
    Rep.res (AlgEquiv.restrictScalarsHom K : (Ks ≃ₐ[E] Ks) →* (Ks ≃ₐ[K] Ks)) (galUnits.{u} K Ks) ⟶
      galUnits.{u} E Ks :=
  Rep.ofHom ⟨uliftIntLinearMap (A := Additive Ksˣ) (B := Additive Ksˣ) (AddMonoidHom.id _),
    fun σ => by
      ext x
      rfl⟩

@[simp]
theorem galUnitsRestrictScalars_hom_apply (E : IntermediateField K Ks) (x : Additive Ksˣ) :
    (galUnitsRestrictScalars E).hom x = x :=
  rfl

end Topology

section Main

variable {K Ks : Type u} [Field K] [Field Ks] [Algebra K Ks] [IsSepClosure K Ks]

instance isSepClosure_intermediateField (E : IntermediateField K Ks) : IsSepClosure E Ks :=
  ⟨IsSepClosure.sep_closed K, Algebra.isSeparable_tower_top_of_isSeparable K E Ks⟩

variable (E : IntermediateField K Ks)

def restrictionH2 :
    Multiplicative (cohomologicalBrauerGroup K Ks) →* Multiplicative (cohomologicalBrauerGroup E Ks) :=
  AddMonoidHom.toMultiplicative
    (cohomologyMapAlong (AlgEquiv.restrictScalarsHom K) (continuous_restrictScalarsHom E)
      (galUnitsRestrictScalars E) 2).hom.toAddMonoidHom

def toFixingSubgroup : (Ks ≃ₐ[E] Ks) →* E.fixingSubgroup :=
  (AlgEquiv.restrictScalarsHom K).codRestrict E.fixingSubgroup fun σ =>
    (IntermediateField.mem_fixingSubgroup_iff _ _).2 fun x hx => σ.commutes ⟨x, hx⟩

instance isDiscreteRep_res_fixingSubgroup :
    IsDiscreteRep (Rep.res E.fixingSubgroup.subtype (galUnits.{u} K Ks)) :=
  isDiscreteRep_res_subtype _ _

end Main

end GroundTheory.Brauer
