import Mathlib
import GroundTheory.ProfiniteCohomology.CupProducts.Pairing
import GroundTheory.ProfiniteCohomology.GaloisCohomology.UnitsInflationCochainsFHomApply
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.ProfCoh

open CategoryTheory MonoidalCategory

universe u

section Iso

variable {k G : Type*} [CommRing k] [Monoid G]

def Rep.isoOfBijective {A B : Rep.{u} k G} (f : A ⟶ B) (hf : Function.Bijective f.hom) :
    A ≅ B :=
  Rep.mkIso (Representation.IntertwiningMap.ofBijective f.hom hf)

@[simp]
theorem Rep.isoOfBijective_hom {A B : Rep.{u} k G} (f : A ⟶ B) (hf : Function.Bijective f.hom) :
    (Rep.isoOfBijective f hf).hom = f :=
  rfl

end Iso

section ZMod

variable (G : Type*) [Monoid G]

abbrev zmodRep (n : ℕ) : Rep.{u} (ULift.{u} ℤ) G :=
  Rep.trivial (ULift.{u} ℤ) G (ULift.{u} (ZMod n))

end ZMod

attribute [local instance 2000] Rep.hV2

variable (K L : Type u) [Field K] [Field L] [Algebra K L]

abbrev cartierDual (M : Rep.{u} (ULift.{u} ℤ) Gal(L/K)) : Rep.{u} (ULift.{u} ℤ) Gal(L/K) :=
  Rep.of (Representation.linHom M.ρ (galUnits.{u} K L).ρ)

variable {K L}

theorem cartierDual_ρ_apply (M : Rep.{u} (ULift.{u} ℤ) Gal(L/K)) (σ : Gal(L/K))
    (f : M →ₗ[ULift.{u} ℤ] galUnits.{u} K L) (m : M) :
    ((cartierDual K L M).ρ σ f : M →ₗ[ULift.{u} ℤ] galUnits.{u} K L) m =
      (galUnits.{u} K L).ρ σ (f (M.ρ σ⁻¹ m)) :=
  rfl

theorem coe_cartierDual_ρ_apply (M : Rep.{u} (ULift.{u} ℤ) Gal(L/K)) (σ : Gal(L/K))
    (f : M →ₗ[ULift.{u} ℤ] galUnits.{u} K L) (m : M) :
    ((Additive.toMul (((cartierDual K L M).ρ σ f : M →ₗ[ULift.{u} ℤ] galUnits.{u} K L) m) :
      Lˣ) : L) =
      σ ((Additive.toMul (f (M.ρ σ⁻¹ m)) : Lˣ) : L) :=
  rfl

def cartierDualMap {A B : Rep.{u} (ULift.{u} ℤ) Gal(L/K)} (φ : A ⟶ B) :
    cartierDual K L B ⟶ cartierDual K L A :=
  Rep.ofHom ⟨{ toFun := fun f => f ∘ₗ φ.hom.toLinearMap
               map_add' := fun f g => rfl
               map_smul' := fun r f => rfl }, fun σ => by
    refine LinearMap.ext fun f => LinearMap.ext fun a => ?_
    change (galUnits.{u} K L).ρ σ (f (B.ρ σ⁻¹ (φ.hom a))) =
      (galUnits.{u} K L).ρ σ (f (φ.hom (A.ρ σ⁻¹ a)))
    rw [Rep.hom_comm_apply]⟩

@[simp]
theorem cartierDualMap_hom_apply {A B : Rep.{u} (ULift.{u} ℤ) Gal(L/K)} (φ : A ⟶ B)
    (f : B →ₗ[ULift.{u} ℤ] galUnits.{u} K L) (a : A) :
    ((cartierDualMap φ).hom f : A →ₗ[ULift.{u} ℤ] galUnits.{u} K L) a = f (φ.hom a) :=
  rfl

theorem cartierDualMap_id (A : Rep.{u} (ULift.{u} ℤ) Gal(L/K)) :
    cartierDualMap (𝟙 A) = 𝟙 (cartierDual K L A) :=
  rfl

theorem cartierDualMap_comp {A B C : Rep.{u} (ULift.{u} ℤ) Gal(L/K)} (φ : A ⟶ B) (ψ : B ⟶ C) :
    cartierDualMap (φ ≫ ψ) = cartierDualMap ψ ≫ cartierDualMap (K := K) (L := L) φ :=
  rfl

variable (K L)

def cartierDualFunctor :
    (Rep.{u} (ULift.{u} ℤ) Gal(L/K))ᵒᵖ ⥤ Rep.{u} (ULift.{u} ℤ) Gal(L/K) where
  obj M := cartierDual K L M.unop
  map φ := cartierDualMap φ.unop
  map_id M := cartierDualMap_id M.unop
  map_comp φ ψ := cartierDualMap_comp ψ.unop φ.unop

@[simp]
theorem cartierDualFunctor_obj (M : (Rep.{u} (ULift.{u} ℤ) Gal(L/K))ᵒᵖ) :
    (cartierDualFunctor K L).obj M = cartierDual K L M.unop :=
  rfl

@[simp]
theorem cartierDualFunctor_map {M N : (Rep.{u} (ULift.{u} ℤ) Gal(L/K))ᵒᵖ} (φ : M ⟶ N) :
    (cartierDualFunctor K L).map φ = cartierDualMap φ.unop :=
  rfl

def evalBilin (M : Rep.{u} (ULift.{u} ℤ) Gal(L/K)) :
    M →ₗ[ULift.{u} ℤ] (M →ₗ[ULift.{u} ℤ] galUnits.{u} K L) →ₗ[ULift.{u} ℤ] galUnits.{u} K L where
  toFun m :=
    { toFun := fun f => f m
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  map_add' a b := LinearMap.ext fun f => f.map_add a b
  map_smul' r a := LinearMap.ext fun f => f.map_smul r a

def cartierPairing (M : Rep.{u} (ULift.{u} ℤ) Gal(L/K)) :
    M ⊗ cartierDual K L M ⟶ galUnits.{u} K L :=
  pairingHom (evalBilin K L M) fun σ m f => by
    change (galUnits.{u} K L).ρ σ (f (M.ρ σ⁻¹ (M.ρ σ m))) = (galUnits.{u} K L).ρ σ (f m)
    rw [Representation.inv_self_apply]

variable {K L}

@[simp]
theorem cartierPairing_tmul (M : Rep.{u} (ULift.{u} ℤ) Gal(L/K)) (m : M)
    (f : M →ₗ[ULift.{u} ℤ] galUnits.{u} K L) :
    (cartierPairing K L M).hom (m ⊗ₜ[ULift.{u} ℤ] (f : cartierDual K L M) :
      (M ⊗ cartierDual K L M : Rep _ _)) = f m :=
  pairingHom_tmul (A := M) (B := cartierDual K L M) (evalBilin K L M) _ m f

variable (K L)

def toCartierDualCartierDual (M : Rep.{u} (ULift.{u} ℤ) Gal(L/K)) :
    M ⟶ cartierDual K L (cartierDual K L M) :=
  Rep.ofHom ⟨evalBilin K L M, fun σ => by
    refine LinearMap.ext fun m => LinearMap.ext fun f => ?_
    change f (M.ρ σ m) = (galUnits.{u} K L).ρ σ ((galUnits.{u} K L).ρ σ⁻¹
      (f (M.ρ σ⁻¹⁻¹ m)))
    rw [inv_inv, Representation.self_inv_apply]⟩

variable {K L}

@[simp]
theorem toCartierDualCartierDual_hom_apply (M : Rep.{u} (ULift.{u} ℤ) Gal(L/K)) (m : M)
    (f : M →ₗ[ULift.{u} ℤ] galUnits.{u} K L) :
    ((toCartierDualCartierDual K L M).hom m :
      (M →ₗ[ULift.{u} ℤ] galUnits.{u} K L) →ₗ[ULift.{u} ℤ] galUnits.{u} K L) f = f m :=
  rfl

end GroundTheory.ProfCoh
