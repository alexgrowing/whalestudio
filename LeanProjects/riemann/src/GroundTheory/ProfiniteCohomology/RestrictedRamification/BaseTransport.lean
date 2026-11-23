import Mathlib
import GroundTheory.ProfiniteCohomology.RestrictedRamification.BaseChangeModules
import GroundTheory.ProfiniteCohomology.PoincarePairs.ConeProduct
import GroundTheory.ProfiniteCohomology.PoincarePairs.MackeyCup
set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open CategoryTheory MonoidalCategory GroundTheory.GroupCoh

universe u

noncomputable section

section Transport

variable {k G G' : Type u} [CommRing k] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [Group G'] [TopologicalSpace G'] [IsTopologicalGroup G'] {ι ι' : Type u} {H : ι → Type u}
  {H' : ι' → Type u} [∀ i, Group (H i)] [∀ i, TopologicalSpace (H i)] [∀ i, IsTopologicalGroup (H i)]
  [∀ j, Group (H' j)] [∀ j, TopologicalSpace (H' j)] [∀ j, IsTopologicalGroup (H' j)]
  (φ : ∀ i, H i →ₜ* G) (φ' : ∀ j, H' j →ₜ* G') (θ : G ≃ₜ* G') (e : ι ≃ ι') (ψ : ∀ i, H i ≃ₜ* H' (e i))
  (hcomm : ∀ i h, θ (φ i h) = φ' (e i) (ψ i h))

section Cochains

variable {A' : Rep.{u} k G'} [IsDiscreteRep A'] {A : Rep.{u} k G} [IsDiscreteRep A]
  (f : Rep.res θ.toMulEquiv.toMonoidHom A' ⟶ A)

def transportLocalMor (i : ι) :
    Rep.res (ψ i).toMulEquiv.toMonoidHom (Rep.res (φ' (e i)).toMonoidHom A') ⟶
      Rep.res (φ i).toMonoidHom A :=
  Rep.ofHom ⟨f.hom.toLinearMap, fun h => LinearMap.ext fun a => by
    change f.hom (A'.ρ (φ' (e i) (ψ i h)) a) = A.ρ (φ i h) (f.hom a)
    rw [← hcomm]
    exact Rep.hom_comm_apply f (φ i h) a⟩

omit [IsTopologicalGroup G] [IsTopologicalGroup G'] [∀ i, IsTopologicalGroup (H i)]
  [∀ j, IsTopologicalGroup (H' j)] [IsDiscreteRep A'] [IsDiscreteRep A] in
theorem transportLocalMor_hom_apply (i : ι) (a : A') :
    (transportLocalMor φ φ' θ e ψ hcomm f i).hom a = f.hom a :=
  rfl

abbrev transportGlobal : cochainsComplex A' ⟶ cochainsComplex A :=
  cochainsMapAlong θ.toMulEquiv.toMonoidHom (continuous_mulEquiv_toMonoidHom θ) f

def transportLocal :
    piComplex (fun j => cochainsComplex (Rep.res (φ' j).toMonoidHom A')) ⟶
      piComplex (fun i => cochainsComplex (Rep.res (φ i).toMonoidHom A)) :=
  piLift fun i => piProj (fun j => cochainsComplex (Rep.res (φ' j).toMonoidHom A')) (e i) ≫
    cochainsMapAlong (ψ i).toMulEquiv.toMonoidHom (continuous_mulEquiv_toMonoidHom (ψ i))
      (transportLocalMor φ φ' θ e ψ hcomm f i)

theorem localRes_transportLocal :
    localRes φ' A' (fun j => Rep.res (φ' j).toMonoidHom A') (fun _ => 𝟙 _) ≫
        transportLocal φ φ' θ e ψ hcomm f =
      transportGlobal θ f ≫ localRes φ A (fun i => Rep.res (φ i).toMonoidHom A) (fun _ => 𝟙 _) := by
  refine HomologicalComplex.hom_ext _ _ fun n => ModuleCat.hom_ext (LinearMap.ext fun x =>
    funext fun i => cochainOf_injective (funext fun σ => ?_))
  change f.hom (cochainOf A' x (⇑(φ' (e i)) ∘ ⇑(ψ i) ∘ σ)) = f.hom (cochainOf A' x (⇑θ ∘ ⇑(φ i) ∘ σ))
  congr 2
  funext j
  exact (hcomm i (σ j)).symm

def compactTransportCochains :
    compactCochains φ' A' (fun j => Rep.res (φ' j).toMonoidHom A') (fun _ => 𝟙 _) ⟶
      compactCochains φ A (fun i => Rep.res (φ i).toMonoidHom A) (fun _ => 𝟙 _) :=
  mappingCoconeNat.mapOfHomotopy (Homotopy.ofEq (localRes_transportLocal φ φ' θ e ψ hcomm f))

def compactTransport (n : ℕ) : compactCohomologyRes φ' A' n ⟶ compactCohomologyRes φ A n :=
  HomologicalComplex.homologyMap (compactTransportCochains φ φ' θ e ψ hcomm f) n

theorem compactTransport_compactToGlobal (n : ℕ) :
    compactTransport φ φ' θ e ψ hcomm f n ≫ compactToGlobal φ A _ (fun _ => 𝟙 _) n =
      compactToGlobal φ' A' _ (fun _ => 𝟙 _) n ≫
        cohomologyMapAlong θ.toMulEquiv.toMonoidHom (continuous_mulEquiv_toMonoidHom θ) f n :=
  (HomologicalComplex.homologyMap_comp _ _ n).symm.trans
    ((congrArg (fun ψ => HomologicalComplex.homologyMap ψ n)
      (mappingCoconeNat.mapOfHomotopy_fst _)).trans (HomologicalComplex.homologyMap_comp _ _ n))

def transportLocalCohomology (n : ℕ) :
    ModuleCat.of k (∀ j, cohomology (Rep.res (φ' j).toMonoidHom A') n) ⟶
      ModuleCat.of k (∀ i, cohomology (Rep.res (φ i).toMonoidHom A) n) :=
  ModuleCat.ofHom (LinearMap.pi fun i => (cohomologyMapAlong (ψ i).toMulEquiv.toMonoidHom
    (continuous_mulEquiv_toMonoidHom (ψ i)) (transportLocalMor φ φ' θ e ψ hcomm f i) n).hom.comp
      (LinearMap.proj (e i)))

omit [IsTopologicalGroup G] [IsTopologicalGroup G'] in

theorem homologyMap_transportLocal_localCohomologyIso (n : ℕ) :
    HomologicalComplex.homologyMap (transportLocal φ φ' θ e ψ hcomm f) n ≫
        (localCohomologyIso (fun i => Rep.res (φ i).toMonoidHom A) n).hom =
      (localCohomologyIso (fun j => Rep.res (φ' j).toMonoidHom A') n).hom ≫
        transportLocalCohomology φ φ' θ e ψ hcomm f n := by
  refine ModuleCat.hom_ext (LinearMap.ext fun z => funext fun i => ?_)
  change (HomologicalComplex.homologyMap (piProj _ i) n).hom
      ((HomologicalComplex.homologyMap (transportLocal φ φ' θ e ψ hcomm f) n).hom z) =
    (cohomologyMapAlong (ψ i).toMulEquiv.toMonoidHom (continuous_mulEquiv_toMonoidHom (ψ i))
      (transportLocalMor φ φ' θ e ψ hcomm f i) n).hom
        ((HomologicalComplex.homologyMap (piProj _ (e i)) n).hom z)
  rw [hom_apply_hom_apply_of_comp_eq (HomologicalComplex.homologyMap_comp _ _ n).symm z, transportLocal,
    piLift_piProj, HomologicalComplex.homologyMap_comp]
  rfl

end Cochains

section Iso

variable {A' : Rep.{u} k G'} [IsDiscreteRep A'] {A : Rep.{u} k G} [IsDiscreteRep A]
  (f : Rep.res θ.toMulEquiv.toMonoidHom A' ≅ A)

def transportLocalIso (i : ι) :
    Rep.res (ψ i).toMulEquiv.toMonoidHom (Rep.res (φ' (e i)).toMonoidHom A') ≅
      Rep.res (φ i).toMonoidHom A where
  hom := transportLocalMor φ φ' θ e ψ hcomm f.hom i
  inv := Rep.ofHom ⟨f.inv.hom.toLinearMap, fun h => LinearMap.ext fun a => by
    change f.inv.hom (A.ρ (φ i h) a) = A'.ρ (φ' (e i) (ψ i h)) (f.inv.hom a)
    rw [← hcomm]
    exact Rep.hom_comm_apply f.inv (φ i h) a⟩
  hom_inv_id := Rep.hom_ext (Representation.IntertwiningMap.ext (LinearMap.ext fun a => by
    change f.inv.hom (f.hom.hom (a : A')) = (a : A')
    exact Rep.inv_hom_apply _ _ f a))
  inv_hom_id := Rep.hom_ext (Representation.IntertwiningMap.ext (LinearMap.ext fun a => by
    change f.hom.hom (f.inv.hom (a : A)) = (a : A)
    exact Rep.hom_inv_apply _ _ f a))

omit [IsTopologicalGroup G] [IsTopologicalGroup G'] in
theorem transportLocalCohomology_bijective (n : ℕ) :
    Function.Bijective (transportLocalCohomology φ φ' θ e ψ hcomm f.hom n).hom := by
  have hc : ∀ i, Function.Bijective (cohomologyMapAlong (ψ i).toMulEquiv.toMonoidHom
      (continuous_mulEquiv_toMonoidHom (ψ i)) (transportLocalMor φ φ' θ e ψ hcomm f.hom i) n).hom :=
    fun i => ((cohomologyIsoOfContinuousMulEquiv (ψ i) (transportLocalIso φ φ' θ e ψ hcomm f i) n).toLinearEquiv).bijective
  have h1 : Function.Bijective (fun ξ : ∀ j, cohomology (Rep.res (φ' j).toMonoidHom A') n =>
      fun i => ξ (e i)) :=
    (Equiv.piCongrLeft (fun j => cohomology (Rep.res (φ' j).toMonoidHom A') n) e).symm.bijective
  exact (Function.Bijective.piMap hc).comp h1

instance isIso_homologyMap_transportGlobal (n : ℕ) :
    IsIso (HomologicalComplex.homologyMap (transportGlobal θ f.hom) n) :=
  (cohomologyIsoOfContinuousMulEquiv θ f n).isIso_hom

instance isIso_homologyMap_transportLocal (n : ℕ) :
    IsIso (HomologicalComplex.homologyMap (transportLocal φ φ' θ e ψ hcomm f.hom) n) := by
  have hb := transportLocalCohomology_bijective φ φ' θ e ψ hcomm f n
  have : IsIso (transportLocalCohomology φ φ' θ e ψ hcomm f.hom n) :=
    (ConcreteCategory.isIso_iff_bijective _).2 hb
  have h := homologyMap_transportLocal_localCohomologyIso φ φ' θ e ψ hcomm f.hom n
  rw [← Iso.eq_comp_inv] at h
  rw [h]
  infer_instance

instance isIso_compactTransport (n : ℕ) : IsIso (compactTransport φ φ' θ e ψ hcomm f.hom n) :=
  mappingCoconeNat.isIso_homologyMap_mapOfHomotopy _
    (isIso_homologyMap_transportGlobal θ f) (isIso_homologyMap_transportLocal φ φ' θ e ψ hcomm f) n

def compactTransportIso (n : ℕ) : compactCohomologyRes φ' A' n ≅ compactCohomologyRes φ A n :=
  asIso (compactTransport φ φ' θ e ψ hcomm f.hom n)

end Iso

omit [IsTopologicalGroup G] [IsTopologicalGroup G'] in
theorem homotopy_ofEq_hom_apply {C D : CochainComplex (ModuleCat.{u} k) ℕ} {f g : C ⟶ D} (h : f = g) (i j : ℕ)
    (x : C.X i) : ((Homotopy.ofEq h).hom i j).hom x = 0 :=
  rfl

section CupGeneral

variable {K₁ K₂ : Type u} [Group K₁] [TopologicalSpace K₁] [IsTopologicalGroup K₁] [Group K₂]
  [TopologicalSpace K₂] [IsTopologicalGroup K₂] (ι₀ : K₁ →* K₂) (hι₀ : Continuous ι₀)
  {A B C : Rep.{u} k K₂} [IsDiscreteRep A] [IsDiscreteRep B] [IsDiscreteRep C]
  {A₁ B₁ C₁ : Rep.{u} k K₁} [IsDiscreteRep A₁] [IsDiscreteRep B₁] [IsDiscreteRep C₁]
  (a : Rep.res ι₀ A ⟶ A₁) (b : Rep.res ι₀ B ⟶ B₁) (c : Rep.res ι₀ C ⟶ C₁) (μ : A ⊗ B ⟶ C)
  (μ₁ : A₁ ⊗ B₁ ⟶ C₁) (hμ : (Rep.resFunctor ι₀).map μ ≫ c = resTensorHom ι₀ a b ≫ μ₁)

include hμ in

theorem cochainsMapAlong_cupPairingCochains {r s n : ℕ} (h : r + s = n) (x : (cochainsComplex A).X r)
    (z : (cochainsComplex B).X s) :
    ((cochainsMapAlong ι₀ hι₀ c).f n).hom (cupPairingCochains μ h x z) =
      cupPairingCochains μ₁ h (((cochainsMapAlong ι₀ hι₀ a).f r).hom x)
        (((cochainsMapAlong ι₀ hι₀ b).f s).hom z) := by
  apply cochainOf_injective
  funext σ
  change c.hom (μ.hom (cupCochain h (cochainOf A x) (cochainOf B z) (⇑ι₀ ∘ σ))) =
    μ₁.hom (cupCochain h (fun τ => a.hom (cochainOf A x (⇑ι₀ ∘ τ)))
      (fun τ => b.hom (cochainOf B z (⇑ι₀ ∘ τ))) σ)
  rw [cupCochain_apply, cupCochain_apply, ← Rep.hom_comm_apply, partialProd_comp_monoidHom]
  exact congrArg (fun F : Rep.res ι₀ (A ⊗ B) ⟶ C₁ => F.hom
    ((cochainOf A x fun i => (⇑ι₀ ∘ σ) ⟨i, by omega⟩) ⊗ₜ[k]
      B.ρ (ι₀ (Fin.partialProd σ ⟨r, by omega⟩))
        (cochainOf B z fun j => (⇑ι₀ ∘ σ) ⟨r + j, by omega⟩) :
      (A ⊗ B : Rep k K₂))) hμ

end CupGeneral

section Cup

variable {A' B' C' : Rep.{u} k G'} [IsDiscreteRep A'] [IsDiscreteRep B'] [IsDiscreteRep C']
  {A B C : Rep.{u} k G} [IsDiscreteRep A] [IsDiscreteRep B] [IsDiscreteRep C]
  (fA : Rep.res θ.toMulEquiv.toMonoidHom A' ⟶ A) (fB : Rep.res θ.toMulEquiv.toMonoidHom B' ⟶ B)
  (fC : Rep.res θ.toMulEquiv.toMonoidHom C' ⟶ C) (μ' : A' ⊗ B' ⟶ C') (μ : A ⊗ B ⟶ C)
  (hμ : (Rep.resFunctor θ.toMulEquiv.toMonoidHom).map μ' ≫ fC =
    resTensorHom θ.toMulEquiv.toMonoidHom fA fB ≫ μ)

omit [IsTopologicalGroup G] [IsTopologicalGroup G'] [∀ i, IsTopologicalGroup (H i)]
  [∀ j, IsTopologicalGroup (H' j)] [IsDiscreteRep A'] [IsDiscreteRep B'] [IsDiscreteRep C']
  [IsDiscreteRep A] [IsDiscreteRep B] [IsDiscreteRep C] in
include hμ in

theorem transportLocalMor_pairing (i : ι) :
    (Rep.resFunctor (ψ i).toMulEquiv.toMonoidHom).map ((Rep.resFunctor (φ' (e i)).toMonoidHom).map μ') ≫
        transportLocalMor φ φ' θ e ψ hcomm fC i =
      resTensorHom (ψ i).toMulEquiv.toMonoidHom (transportLocalMor φ φ' θ e ψ hcomm fA i)
        (transportLocalMor φ φ' θ e ψ hcomm fB i) ≫ (Rep.resFunctor (φ i).toMonoidHom).map μ := by
  apply Rep.hom_ext
  apply Representation.IntertwiningMap.ext
  apply TensorProduct.ext'
  intro a b
  change fC.hom (μ'.hom ((a : A') ⊗ₜ[k] (b : B') : (A' ⊗ B' : Rep k G'))) =
    μ.hom ((fA.hom a ⊗ₜ[k] fB.hom b : (A ⊗ B : Rep k G)))
  exact congrArg (fun F : Rep.res θ.toMulEquiv.toMonoidHom (A' ⊗ B') ⟶ C =>
    F.hom ((a : A') ⊗ₜ[k] (b : B') : (A' ⊗ B' : Rep k G'))) hμ

omit [IsTopologicalGroup G] [IsTopologicalGroup G'] in
include hμ in

theorem transportLocal_pi_cup {r s n : ℕ} (hh : r + s = n)
    (y₀ : (piComplex fun j => cochainsComplex (Rep.res (φ' j).toMonoidHom A')).X r)
    (w₀ : (piComplex fun j => cochainsComplex (Rep.res (φ' j).toMonoidHom B')).X s) :
    ((transportLocal φ φ' θ e ψ hcomm fC).f n).hom
        ((LeibnizPairing.pi fun j => cupLeibniz (A := Rep.res (φ' j).toMonoidHom A') (B := Rep.res (φ' j).toMonoidHom B')
        (C := Rep.res (φ' j).toMonoidHom C') ((Rep.resFunctor (φ' j).toMonoidHom).map μ')).μ hh y₀ w₀) =
      (LeibnizPairing.pi fun i => cupLeibniz (A := Rep.res (φ i).toMonoidHom A) (B := Rep.res (φ i).toMonoidHom B)
        (C := Rep.res (φ i).toMonoidHom C) ((Rep.resFunctor (φ i).toMonoidHom).map μ)).μ hh
        (((transportLocal φ φ' θ e ψ hcomm fA).f r).hom y₀) (((transportLocal φ φ' θ e ψ hcomm fB).f s).hom w₀) := by
  funext i
  change ((cochainsMapAlong (ψ i).toMulEquiv.toMonoidHom (continuous_mulEquiv_toMonoidHom (ψ i))
      (transportLocalMor φ φ' θ e ψ hcomm fC i)).f n).hom
        (cupPairingCochains (A := Rep.res (φ' (e i)).toMonoidHom A') (B := Rep.res (φ' (e i)).toMonoidHom B')
          (C := Rep.res (φ' (e i)).toMonoidHom C') ((Rep.resFunctor (φ' (e i)).toMonoidHom).map μ') hh
          (y₀ (e i)) (w₀ (e i))) =
    cupPairingCochains (A := Rep.res (φ i).toMonoidHom A) (B := Rep.res (φ i).toMonoidHom B)
      (C := Rep.res (φ i).toMonoidHom C) ((Rep.resFunctor (φ i).toMonoidHom).map μ) hh
      (((cochainsMapAlong (ψ i).toMulEquiv.toMonoidHom (continuous_mulEquiv_toMonoidHom (ψ i))
        (transportLocalMor φ φ' θ e ψ hcomm fA i)).f r).hom (y₀ (e i)))
      (((cochainsMapAlong (ψ i).toMulEquiv.toMonoidHom (continuous_mulEquiv_toMonoidHom (ψ i))
        (transportLocalMor φ φ' θ e ψ hcomm fB i)).f s).hom (w₀ (e i)))
  exact cochainsMapAlong_cupPairingCochains (ψ i).toMulEquiv.toMonoidHom (continuous_mulEquiv_toMonoidHom (ψ i))
    (A := Rep.res (φ' (e i)).toMonoidHom A') (B := Rep.res (φ' (e i)).toMonoidHom B')
    (C := Rep.res (φ' (e i)).toMonoidHom C') (A₁ := Rep.res (φ i).toMonoidHom A)
    (B₁ := Rep.res (φ i).toMonoidHom B) (C₁ := Rep.res (φ i).toMonoidHom C)
    (transportLocalMor φ φ' θ e ψ hcomm fA i) (transportLocalMor φ φ' θ e ψ hcomm fB i)
    (transportLocalMor φ φ' θ e ψ hcomm fC i) ((Rep.resFunctor (φ' (e i)).toMonoidHom).map μ')
    ((Rep.resFunctor (φ i).toMonoidHom).map μ)
    (transportLocalMor_pairing φ φ' θ e ψ hcomm fA fB fC μ' μ hμ i) hh (y₀ (e i)) (w₀ (e i))

include hμ in

theorem compactTransport_compactCupRes {r s n : ℕ} (h : r + s = n) (y : compactCohomologyRes φ' A' r)
    (x : cohomology B' s) :
    (compactTransport φ φ' θ e ψ hcomm fC n).hom (compactCupRes φ' μ' h y x) =
      compactCupRes φ μ h ((compactTransport φ φ' θ e ψ hcomm fA r).hom y)
        ((cohomologyMapAlong θ.toMulEquiv.toMonoidHom (continuous_mulEquiv_toMonoidHom θ) fB s).hom x) := by
  have hc := fun {r s n : ℕ} (hh : r + s = n) (x₀ : (cochainsComplex A').X r)
      (z₀ : (cochainsComplex B').X s) =>
    localRes_cupPairingCochains φ' μ'
      (Aᵥ := fun j => Rep.res (φ' j).toMonoidHom A') (Bᵥ := fun j => Rep.res (φ' j).toMonoidHom B')
      (Cᵥ := fun j => Rep.res (φ' j).toMonoidHom C')
      (a := fun _ => 𝟙 _) (b := fun _ => 𝟙 _) (c := fun _ => 𝟙 _)
      (fun j => (Rep.resFunctor (φ' j).toMonoidHom).map μ')
      (fun j => resFunctor_map_comp_id (φ' j).toMonoidHom _) hh x₀ z₀
  have hc' := fun {r s n : ℕ} (hh : r + s = n) (x₀ : (cochainsComplex A).X r)
      (z₀ : (cochainsComplex B).X s) =>
    localRes_cupPairingCochains φ μ
      (Aᵥ := fun i => Rep.res (φ i).toMonoidHom A) (Bᵥ := fun i => Rep.res (φ i).toMonoidHom B)
      (Cᵥ := fun i => Rep.res (φ i).toMonoidHom C)
      (a := fun _ => 𝟙 _) (b := fun _ => 𝟙 _) (c := fun _ => 𝟙 _)
      (fun i => (Rep.resFunctor (φ i).toMonoidHom).map μ)
      (fun i => resFunctor_map_comp_id (φ i).toMonoidHom _) hh x₀ z₀
  exact mappingCoconeNat.homologyMap_mapOfHomotopy_coconeLeft
    (Homotopy.ofEq (localRes_transportLocal φ φ' θ e ψ hcomm fA))
    (Homotopy.ofEq (localRes_transportLocal φ φ' θ e ψ hcomm fC))
    (Homotopy.ofEq (localRes_transportLocal φ φ' θ e ψ hcomm fB))
    (LeibnizPairing.pi fun j => cupLeibniz (A := Rep.res (φ' j).toMonoidHom A') (B := Rep.res (φ' j).toMonoidHom B')
        (C := Rep.res (φ' j).toMonoidHom C') ((Rep.resFunctor (φ' j).toMonoidHom).map μ'))
    (cupLeibniz μ')
    (LeibnizPairing.pi fun i => cupLeibniz (A := Rep.res (φ i).toMonoidHom A) (B := Rep.res (φ i).toMonoidHom B)
        (C := Rep.res (φ i).toMonoidHom C) ((Rep.resFunctor (φ i).toMonoidHom).map μ))
    (cupLeibniz μ) hc hc'
    (fun hh x₀ z₀ => cochainsMapAlong_cupPairingCochains _ _ fA fB fC μ' μ hμ hh x₀ z₀)
    (fun hh y₀ w₀ => transportLocal_pi_cup φ φ' θ e ψ hcomm fA fB fC μ' μ hμ hh y₀ w₀)
    (fun _ _ _ => by
      rw [homotopy_ofEq_hom_apply, homotopy_ofEq_hom_apply, homotopy_ofEq_hom_apply, LinearMap.map_zero₂,
        map_zero, smul_zero, add_zero])
    (fun _ _ _ => by rw [homotopy_ofEq_hom_apply, homotopy_ofEq_hom_apply, map_zero])
    (fun _ _ _ => by rw [homotopy_ofEq_hom_apply, homotopy_ofEq_hom_apply, LinearMap.map_zero₂]) h y x

end Cup

end Transport

end

end GroundTheory.ProfCoh
