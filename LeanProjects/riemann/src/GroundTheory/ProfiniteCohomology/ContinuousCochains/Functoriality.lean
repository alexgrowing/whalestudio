import Mathlib
import GroundTheory.ProfiniteCohomology.ContinuousCochains
set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open CategoryTheory groupCohomology

universe u

variable {k G : Type u} [CommRing k] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

section Map

variable {A B C : Rep.{u} k G} [IsDiscreteRep A] [IsDiscreteRep B] [IsDiscreteRep C]

noncomputable def cochainsMapLinear (f : A ⟶ B) (n : ℕ) :
    locallyConstantCochains A n →ₗ[k] locallyConstantCochains B n :=
  (f.hom.toLinearMap.compLeft (Fin n → G)).restrict fun _ hc => IsLocallyConstant.comp hc _

omit [IsTopologicalGroup G] [IsDiscreteRep A] [IsDiscreteRep B] in
@[simp]
theorem cochainsMapLinear_apply (f : A ⟶ B) (n : ℕ) (c : locallyConstantCochains A n)
    (x : Fin n → G) : (cochainsMapLinear f n c : (Fin n → G) → B) x = f.hom ((c : _ → A) x) :=
  rfl

noncomputable def cochainsMap (f : A ⟶ B) : cochainsComplex A ⟶ cochainsComplex B :=
  CochainComplex.ofHom (fun n => ModuleCat.ofHom (cochainsMapLinear f n)) fun n => by
    rw [cochainsComplex_d, cochainsComplex_d]
    ext c₀ : 2
    let c : locallyConstantCochains A n := c₀
    apply Subtype.ext
    funext g
    change (inhomogeneousCochains.d B n).hom (fun x => f.hom (c.1 x)) g =
      f.hom ((inhomogeneousCochains.d A n).hom c.1 g)
    simp [inhomogeneousCochains.d_hom_apply, Rep.hom_comm_apply, map_add, map_sum, map_smul]

theorem cochainsMap_f_hom_apply (f : A ⟶ B) (n : ℕ) (c : locallyConstantCochains A n) :
    ((cochainsMap f).f n).hom c = cochainsMapLinear f n c :=
  rfl

@[simp]
theorem cochainsMap_id : cochainsMap (𝟙 A) = 𝟙 (cochainsComplex A) := by
  ext n c : 3
  rfl

@[simp]
theorem cochainsMap_comp (f : A ⟶ B) (g : B ⟶ C) :
    cochainsMap (f ≫ g) = cochainsMap f ≫ cochainsMap g := by
  ext n c : 3
  rfl

theorem cochainsMap_comp_cochainsComplexι (f : A ⟶ B) :
    cochainsMap f ≫ cochainsComplexι B =
      cochainsComplexι A ≫ groupCohomology.cochainsMap (MonoidHom.id G) f := by
  ext n c : 3
  rfl

instance (f : A ⟶ B) [Mono f] (n : ℕ) : Mono ((cochainsMap f).f n) := by
  rw [ModuleCat.mono_iff_injective]
  intro c d h
  apply Subtype.ext
  funext x
  exact (Rep.mono_iff_injective f).1 ‹_› (congrFun (congrArg Subtype.val h) x)

instance (f : A ⟶ B) [Epi f] (n : ℕ) : Epi ((cochainsMap f).f n) := by
  rw [ModuleCat.epi_iff_surjective]
  intro d
  obtain ⟨s, hs⟩ := ((Rep.epi_iff_surjective f).1 ‹_›).hasRightInverse
  let d' : locallyConstantCochains B n := d
  refine ⟨(⟨s ∘ d'.1, (mem_locallyConstantCochains A _).2 (IsLocallyConstant.comp d'.2 s)⟩ :
    locallyConstantCochains A n), Subtype.ext ?_⟩
  funext x
  exact hs _

noncomputable def cohomologyMap (f : A ⟶ B) (n : ℕ) : cohomology A n ⟶ cohomology B n :=
  HomologicalComplex.homologyMap (cochainsMap f) n

@[simp]
theorem cohomologyMap_id (n : ℕ) : cohomologyMap (𝟙 A) n = 𝟙 (cohomology A n) := by
  simp [cohomologyMap, cohomology]

theorem cohomologyMap_comp (f : A ⟶ B) (g : B ⟶ C) (n : ℕ) :
    cohomologyMap (f ≫ g) n = cohomologyMap f n ≫ cohomologyMap g n := by
  rw [cohomologyMap, cochainsMap_comp]
  exact HomologicalComplex.homologyMap_comp _ _ _

theorem cohomologyπ_comp_cohomologyMap (f : A ⟶ B) (n : ℕ) :
    cohomologyπ A n ≫ cohomologyMap f n =
      HomologicalComplex.cyclesMap (cochainsMap f) n ≫ cohomologyπ B n :=
  HomologicalComplex.homologyπ_naturality _ _

end Map

section Functor

variable (k G)

@[simps]
noncomputable def cochainsFunctor : DiscreteRep.{u} k G ⥤ CochainComplex (ModuleCat k) ℕ where
  obj A := cochainsComplex A.obj
  map f := cochainsMap f.hom
  map_id _ := cochainsMap_id
  map_comp f g := cochainsMap_comp f.hom g.hom

noncomputable def cohomologyFunctor (n : ℕ) : DiscreteRep.{u} k G ⥤ ModuleCat k :=
  cochainsFunctor k G ⋙ HomologicalComplex.homologyFunctor _ _ n

theorem cohomologyFunctor_obj (n : ℕ) (A : DiscreteRep.{u} k G) :
    (cohomologyFunctor k G n).obj A = cohomology A.obj n :=
  rfl

theorem cohomologyFunctor_map (n : ℕ) {A B : DiscreteRep.{u} k G} (f : A ⟶ B) :
    (cohomologyFunctor k G n).map f = cohomologyMap f.hom n :=
  rfl

instance : (cochainsFunctor k G).Additive where
  map_add {_ _ f g} := by
    ext n c : 3
    apply Subtype.ext
    funext x
    rfl

end Functor

section Comparison

variable (A : Rep.{u} k G) [IsDiscreteRep A]

noncomputable def cohomologyToGroupCohomology (n : ℕ) : cohomology A n ⟶ groupCohomology A n :=
  HomologicalComplex.homologyMap (cochainsComplexι A) n

theorem cohomologyMap_comp_cohomologyToGroupCohomology {B : Rep.{u} k G} [IsDiscreteRep B]
    (f : A ⟶ B) (n : ℕ) :
    cohomologyMap f n ≫ cohomologyToGroupCohomology B n =
      cohomologyToGroupCohomology A n ≫ groupCohomology.map (MonoidHom.id G) f n := by
  change HomologicalComplex.homologyMap (cochainsMap f) n ≫
      HomologicalComplex.homologyMap (cochainsComplexι B) n =
    HomologicalComplex.homologyMap (cochainsComplexι A) n ≫
      HomologicalComplex.homologyMap (groupCohomology.cochainsMap (MonoidHom.id G) f) n
  rw [← HomologicalComplex.homologyMap_comp, ← HomologicalComplex.homologyMap_comp,
    cochainsMap_comp_cochainsComplexι]

instance isIso_cochainsComplexι [DiscreteTopology G] : IsIso (cochainsComplexι A) := by
  have : ∀ n, IsIso ((cochainsComplexι A).f n) := fun n => by
    rw [ConcreteCategory.isIso_iff_bijective]
    refine ⟨Subtype.val_injective, fun c => ⟨⟨c, IsLocallyConstant.of_discrete c⟩, rfl⟩⟩
  exact HomologicalComplex.Hom.isIso_of_components _

noncomputable def cohomologyIsoGroupCohomology [DiscreteTopology G] (n : ℕ) :
    cohomology A n ≅ groupCohomology A n :=
  HomologicalComplex.homologyMapIso (asIso (cochainsComplexι A)) n

theorem cohomologyIsoGroupCohomology_hom [DiscreteTopology G] (n : ℕ) :
    (cohomologyIsoGroupCohomology A n).hom = cohomologyToGroupCohomology A n :=
  rfl

end Comparison

section H0

variable (A : Rep.{u} k G) [IsDiscreteRep A]

noncomputable def invariantsToCochains₀ :
    A.ρ.invariants →ₗ[k] locallyConstantCochains A 0 where
  toFun v := ⟨fun _ => v.1, IsLocallyConstant.const _⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

noncomputable def shortComplexH0 : ShortComplex (ModuleCat k) :=
  ShortComplex.mk (ModuleCat.ofHom (invariantsToCochains₀ A)) (dLocallyConstant A 0) (by
    ext v : 2
    apply Subtype.ext
    funext g
    change (inhomogeneousCochains.d A 0).hom (fun _ => v.1) g = 0
    simp [inhomogeneousCochains.d_hom_apply, v.2 (g 0)])

instance : Mono (shortComplexH0 A).f := by
  rw [ModuleCat.mono_iff_injective]
  intro v w h
  apply Subtype.ext
  exact congrFun (congrArg Subtype.val h) Fin.elim0

theorem shortComplexH0_exact : (shortComplexH0 A).Exact := by
  rw [ShortComplex.moduleCat_exact_iff]
  intro c₀ hc
  let c : locallyConstantCochains A 0 := c₀
  have hc' : ∀ g : Fin 1 → G, (inhomogeneousCochains.d A 0).hom c.1 g = 0 := fun g =>
    congrArg (fun x : locallyConstantCochains A (0 + 1) => x.1 g) hc
  refine ⟨⟨c.1 Fin.elim0, fun g => ?_⟩, Subtype.ext ?_⟩
  · have h := hc' fun _ => g
    have hfe : ∀ x : Fin 0 → G, c.1 x = c.1 Fin.elim0 := fun x => by
      rw [Subsingleton.elim x Fin.elim0]
    simp only [inhomogeneousCochains.d_hom_apply, hfe] at h
    exact add_neg_eq_zero.1 (by simpa using h)
  · funext x
    change c.1 Fin.elim0 = c.1 x
    rw [Subsingleton.elim x Fin.elim0]

theorem cochainsComplex_d_zero_one :
    (cochainsComplex A).d 0 1 = dLocallyConstant A 0 :=
  cochainsComplex_d A 0

noncomputable def cocyclesIso₀ : cocycles A 0 ≅ ModuleCat.of k A.ρ.invariants :=
  Limits.KernelFork.mapIsoOfIsLimit ((cochainsComplex A).cyclesIsKernel 0 1 (by simp))
    (shortComplexH0_exact A).fIsKernel
    (Arrow.isoMk (Iso.refl _) (Iso.refl _) (by
      simp only [Arrow.mk_hom, Iso.refl_hom, cochainsComplex_d_zero_one]
      exact (Category.id_comp _).trans (Category.comp_id _).symm))

noncomputable def H0Iso : cohomology A 0 ≅ ModuleCat.of k A.ρ.invariants :=
  (CochainComplex.isoHomologyπ₀ _).symm ≪≫ cocyclesIso₀ A

end H0

end GroundTheory.ProfCoh
