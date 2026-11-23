import Mathlib
import GroundTheory.ProfiniteCohomology.LocalEulerCharacteristic.ConjAction
set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open CategoryTheory groupCohomology

universe u

section Bridge

variable {k k' G : Type u} [CommRing k] [CommRing k'] [Group G] [TopologicalSpace G]

def cochainsAddEquiv {A : Rep.{u} k G} {A' : Rep.{u} k' G} (e : A ≃+ A') (n : ℕ) :
    locallyConstantCochains A n ≃+ locallyConstantCochains A' n where
  toFun x := ⟨fun g => e (x.1 g), x.2.comp e⟩
  invFun x := ⟨fun g => e.symm (x.1 g), x.2.comp e.symm⟩
  left_inv _ := Subtype.ext (funext fun _ => e.symm_apply_apply _)
  right_inv _ := Subtype.ext (funext fun _ => e.apply_symm_apply _)
  map_add' _ _ := Subtype.ext (funext fun _ => map_add e _ _)

@[simp]
theorem cochainsAddEquiv_apply {A : Rep.{u} k G} {A' : Rep.{u} k' G} (e : A ≃+ A') (n : ℕ)
    (x : locallyConstantCochains A n) (g : Fin n → G) :
    (cochainsAddEquiv e n x : (Fin n → G) → A') g = e ((x : (Fin n → G) → A) g) :=
  rfl

variable [IsTopologicalGroup G] {A : Rep.{u} k G} {A' : Rep.{u} k' G} [IsDiscreteRep A]
  [IsDiscreteRep A'] (e : A ≃+ A') (he : ∀ (g : G) (a : A), e (A.ρ g a) = A'.ρ g (e a))

omit [TopologicalSpace G] [IsTopologicalGroup G] [IsDiscreteRep A] [IsDiscreteRep A'] in
include he in

theorem addEquiv_inhomogeneousCochains_d (i : ℕ) (f : (Fin i → G) → A) (g : Fin (i + 1) → G) :
    e ((inhomogeneousCochains.d A i).hom f g) =
      (inhomogeneousCochains.d A' i).hom (fun h => e (f h)) g := by
  rw [inhomogeneousCochains.d_hom_apply, inhomogeneousCochains.d_hom_apply, map_add, map_sum, he]
  congr 1
  refine Finset.sum_congr rfl fun m _ => ?_
  have hk : ∀ (c : ℕ) (a : A), ((-1 : k) ^ c) • a = ((-1 : ℤ) ^ c) • a := fun c a => by
    rw [← Int.cast_smul_eq_zsmul k]
    push_cast
    rfl
  have hk' : ∀ (c : ℕ) (a : A'), ((-1 : k') ^ c) • a = ((-1 : ℤ) ^ c) • a := fun c a => by
    rw [← Int.cast_smul_eq_zsmul k']
    push_cast
    rfl
  rw [hk, hk', map_zsmul]

include he in

theorem cochainsAddEquiv_d (i j : ℕ) (x : (cochainsComplex A).X i) :
    cochainsAddEquiv e j (((cochainsComplex A).d i j).hom x) =
      ((cochainsComplex A').d i j).hom (cochainsAddEquiv e i x) := by
  rcases eq_or_ne (i + 1) j with rfl | hij
  · rw [cochainsComplex_d, cochainsComplex_d]
    apply Subtype.ext
    funext g
    exact addEquiv_inhomogeneousCochains_d e he i x.1 g
  · have h' : ¬ (ComplexShape.up ℕ).Rel i j := hij
    rw [HomologicalComplex.shape _ _ _ h', HomologicalComplex.shape _ _ _ h']
    exact map_zero _

noncomputable def cochainsAbIso (i : ℕ) :
    (forget₂ (ModuleCat.{u} k) Ab).obj ((cochainsComplex A).X i) ≅
      (forget₂ (ModuleCat.{u} k') Ab).obj ((cochainsComplex A').X i) :=
  (cochainsAddEquiv e i).toAddCommGrpIso

noncomputable def cochainsScAbIso (n : ℕ) :
    (forget₂ (ModuleCat.{u} k) Ab).mapShortComplex.obj ((cochainsComplex A).sc n) ≅
      (forget₂ (ModuleCat.{u} k') Ab).mapShortComplex.obj ((cochainsComplex A').sc n) :=
  ShortComplex.isoMk (cochainsAbIso e _) (cochainsAbIso e _) (cochainsAbIso e _)
    (by
      ext x
      exact (cochainsAddEquiv_d e he _ _ x).symm)
    (by
      ext x
      exact (cochainsAddEquiv_d e he _ _ x).symm)

end Bridge

section HomologyAb

variable {k k' : Type u} [CommRing k] [CommRing k']

noncomputable def homologyAbIsoOfAbIso {S₁ : ShortComplex (ModuleCat.{u} k)}
    {S₂ : ShortComplex (ModuleCat.{u} k')}
    (σ : (forget₂ (ModuleCat.{u} k) Ab).mapShortComplex.obj S₁ ≅
      (forget₂ (ModuleCat.{u} k') Ab).mapShortComplex.obj S₂) :
    (ShortComplex.homologyFunctor _ ⋙ forget₂ (ModuleCat.{u} k) Ab).obj S₁ ≅
      (ShortComplex.homologyFunctor _ ⋙ forget₂ (ModuleCat.{u} k') Ab).obj S₂ :=
  ((ShortComplex.homologyFunctorIso (forget₂ (ModuleCat.{u} k) Ab)).app S₁).symm ≪≫
    (ShortComplex.homologyFunctor Ab).mapIso σ ≪≫
    (ShortComplex.homologyFunctorIso (forget₂ (ModuleCat.{u} k') Ab)).app S₂

theorem homologyMap_comp_homologyAbIsoOfAbIso
    {S₁ T₁ : ShortComplex (ModuleCat.{u} k)} {S₂ T₂ : ShortComplex (ModuleCat.{u} k')}
    (φ₁ : S₁ ⟶ T₁) (φ₂ : S₂ ⟶ T₂)
    (σS : (forget₂ (ModuleCat.{u} k) Ab).mapShortComplex.obj S₁ ≅
      (forget₂ (ModuleCat.{u} k') Ab).mapShortComplex.obj S₂)
    (σT : (forget₂ (ModuleCat.{u} k) Ab).mapShortComplex.obj T₁ ≅
      (forget₂ (ModuleCat.{u} k') Ab).mapShortComplex.obj T₂)
    (h : (forget₂ (ModuleCat.{u} k) Ab).mapShortComplex.map φ₁ ≫ σT.hom =
      σS.hom ≫ (forget₂ (ModuleCat.{u} k') Ab).mapShortComplex.map φ₂) :
    (ShortComplex.homologyFunctor _ ⋙ forget₂ (ModuleCat.{u} k) Ab).map φ₁ ≫
        (homologyAbIsoOfAbIso σT).hom =
      (homologyAbIsoOfAbIso σS).hom ≫
        (ShortComplex.homologyFunctor _ ⋙ forget₂ (ModuleCat.{u} k') Ab).map φ₂ := by
  have n1 := (ShortComplex.homologyFunctorIso (forget₂ (ModuleCat.{u} k) Ab)).inv.naturality φ₁
  have n2 := (ShortComplex.homologyFunctorIso (forget₂ (ModuleCat.{u} k') Ab)).hom.naturality φ₂
  have n3 : ((forget₂ (ModuleCat.{u} k) Ab).mapShortComplex ⋙
        ShortComplex.homologyFunctor Ab).map φ₁ ≫ (ShortComplex.homologyFunctor Ab).map σT.hom =
      (ShortComplex.homologyFunctor Ab).map σS.hom ≫
        ((forget₂ (ModuleCat.{u} k') Ab).mapShortComplex ⋙ ShortComplex.homologyFunctor Ab).map φ₂ := by
    rw [Functor.comp_map, Functor.comp_map, ← Functor.map_comp, ← Functor.map_comp, h]
  simp only [homologyAbIsoOfAbIso, Iso.trans_hom, Iso.symm_hom, Iso.app_inv, Iso.app_hom,
    Functor.mapIso_hom, Category.assoc]
  slice_lhs 1 2 => rw [n1]
  slice_lhs 2 3 => rw [n3]
  slice_lhs 3 4 => rw [n2]

end HomologyAb

section Cohomology

variable {k k' G : Type u} [CommRing k] [CommRing k'] [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G] {A : Rep.{u} k G} {A' : Rep.{u} k' G} [IsDiscreteRep A]
  [IsDiscreteRep A'] (e : A ≃+ A') (he : ∀ (g : G) (a : A), e (A.ρ g a) = A'.ρ g (e a))

noncomputable def cohomologyAddEquivOfEquiv (n : ℕ) : cohomology A n ≃+ cohomology A' n :=
  (homologyAbIsoOfAbIso (cochainsScAbIso e he n)).addCommGroupIsoToAddEquiv

theorem cohomologyAddEquivOfEquiv_mapAlong {H : Type u} [Group H] [TopologicalSpace H]
    [IsTopologicalGroup H] (φ : H →* G) (hφ : Continuous φ) {B : Rep.{u} k H} {B' : Rep.{u} k' H}
    [IsDiscreteRep B] [IsDiscreteRep B'] (eB : B ≃+ B')
    (heB : ∀ (h : H) (b : B), eB (B.ρ h b) = B'.ρ h (eB b))
    (f : Rep.res φ A ⟶ B) (f' : Rep.res φ A' ⟶ B') (hf : ∀ a : A, eB (f.hom a) = f'.hom (e a))
    (n : ℕ) (x : cohomology A n) :
    cohomologyAddEquivOfEquiv eB heB n ((cohomologyMapAlong φ hφ f n).hom x) =
      (cohomologyMapAlong φ hφ f' n).hom (cohomologyAddEquivOfEquiv e he n x) := by
  have key := homologyMap_comp_homologyAbIsoOfAbIso
    ((HomologicalComplex.shortComplexFunctor _ _ n).map (cochainsMapAlong φ hφ f))
    ((HomologicalComplex.shortComplexFunctor _ _ n).map (cochainsMapAlong φ hφ f'))
    (cochainsScAbIso e he n) (cochainsScAbIso eB heB n) (by
      ext x <;> exact Subtype.ext (funext fun _ => hf _))
  exact congrArg (fun f => f.hom x) key

theorem cohomologyAddEquivOfEquiv_cohomologyRes (S : Subgroup G) (n : ℕ) (x : cohomology A n) :
    cohomologyAddEquivOfEquiv (A := Rep.res S.subtype A) (A' := Rep.res S.subtype A') e
        (fun s a => he s a) n ((cohomologyRes A S n).hom x) =
      (cohomologyRes A' S n).hom (cohomologyAddEquivOfEquiv e he n x) := by
  rw [cohomologyRes_eq, cohomologyRes_eq]
  exact cohomologyAddEquivOfEquiv_mapAlong e he S.subtype (continuous_subgroup_subtype S)
    (B := Rep.res S.subtype A) (B' := Rep.res S.subtype A') e (fun s a => he s a) (𝟙 _) (𝟙 _)
    (fun _ => rfl) n x

theorem cohomologyAddEquivOfEquiv_cohomologyMap {B : Rep.{u} k G} {B' : Rep.{u} k' G}
    [IsDiscreteRep B] [IsDiscreteRep B'] (eB : B ≃+ B')
    (heB : ∀ (g : G) (b : B), eB (B.ρ g b) = B'.ρ g (eB b))
    (f : A ⟶ B) (f' : A' ⟶ B') (hf : ∀ a : A, eB (f.hom a) = f'.hom (e a)) (n : ℕ)
    (x : cohomology A n) :
    cohomologyAddEquivOfEquiv eB heB n ((cohomologyMap f n).hom x) =
      (cohomologyMap f' n).hom (cohomologyAddEquivOfEquiv e he n x) := by
  have key := cohomologyAddEquivOfEquiv_mapAlong e he (MonoidHom.id G) continuous_id eB heB f f'
    hf n x
  rwa [cohomologyMapAlong_id_eq_cohomologyMap, cohomologyMapAlong_id_eq_cohomologyMap] at key

theorem cohomologyAddEquivOfEquiv_cohomologyConj (N : Subgroup G) [N.Normal] (n : ℕ) (g : G)
    (x : cohomology (Rep.res N.subtype A) n) :
    cohomologyAddEquivOfEquiv (A := Rep.res N.subtype A) (A' := Rep.res N.subtype A') e
        (fun s a => he s a) n ((cohomologyConj A N n g).hom x) =
      (cohomologyConj A' N n g).hom
        (cohomologyAddEquivOfEquiv (A := Rep.res N.subtype A) (A' := Rep.res N.subtype A') e
          (fun s a => he s a) n x) :=
  cohomologyAddEquivOfEquiv_mapAlong (A := Rep.res N.subtype A) (A' := Rep.res N.subtype A') e
    (fun s a => he s a) (GroundTheory.GroupCoh.conjHom N g) (continuous_conjHom N g)
    (B := Rep.res N.subtype A) (B' := Rep.res N.subtype A') e (fun s a => he s a)
    (GroundTheory.GroupCoh.conjMor A N g) (GroundTheory.GroupCoh.conjMor A' N g) (fun a => he g a) n x

end Cohomology

section ZMod

variable {G : Type} [Group G] (l : ℕ) (A : Rep.{0} (ULift.{0} ℤ) G)
  (hA : ∀ a : A, l • a = 0)

noncomputable def zmodRepOfTorsion : Rep.{0} (ZMod l) G :=
  letI : Module (ZMod l) A := AddCommGroup.zmodModule hA
  Rep.of (X := A)
    { toFun := fun g => (A.ρ g).toAddMonoidHom.toZModLinearMap l
      map_one' := by
        ext a
        simp
      map_mul' := fun g h => by
        ext a
        simp [Module.End.mul_apply] }

theorem zmodRepOfTorsion_ρ_apply (g : G) (a : A) :
    (zmodRepOfTorsion l A hA).ρ g a = A.ρ g a :=
  rfl

def zmodRepOfTorsionEquiv : A ≃+ zmodRepOfTorsion l A hA :=
  AddEquiv.refl A

theorem zmodRepOfTorsionEquiv_apply (a : A) : zmodRepOfTorsionEquiv l A hA a = a :=
  rfl

variable [TopologicalSpace G]

instance isDiscreteRep_zmodRepOfTorsion [IsDiscreteRep A] :
    IsDiscreteRep (zmodRepOfTorsion l A hA) :=
  ⟨fun a => isOpen_stabilizer A a⟩

variable [IsTopologicalGroup G] [IsDiscreteRep A]

noncomputable def cohomologyZModEquiv (n : ℕ) :
    cohomology A n ≃+ cohomology (zmodRepOfTorsion l A hA) n :=
  cohomologyAddEquivOfEquiv (zmodRepOfTorsionEquiv l A hA) (fun _ _ => rfl) n

end ZMod

end GroundTheory.ProfCoh
