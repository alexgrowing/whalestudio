import Mathlib
import GroundTheory.ProfiniteCohomology.CupProducts.Functoriality
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.ProfCoh

open CategoryTheory MonoidalCategory TensorProduct groupCohomology GroundTheory.GroupCoh

universe u

variable {k G : Type u} [CommRing k] [Group G]

section PairingHom

variable {A B C : Rep.{u} k G}

def pairingHom (β : A →ₗ[k] B →ₗ[k] C)
    (hβ : ∀ (g : G) (a : A) (b : B), β (A.ρ g a) (B.ρ g b) = C.ρ g (β a b)) : A ⊗ B ⟶ C :=
  Rep.ofHom ⟨TensorProduct.lift β, fun g => TensorProduct.ext' fun a b => by
    simpa using hβ g a b⟩

@[simp]
theorem pairingHom_tmul (β : A →ₗ[k] B →ₗ[k] C)
    (hβ : ∀ (g : G) (a : A) (b : B), β (A.ρ g a) (B.ρ g b) = C.ρ g (β a b)) (a : A) (b : B) :
    (pairingHom β hβ).hom (a ⊗ₜ[k] b : (A ⊗ B : Rep k G)) = β a b :=
  TensorProduct.lift.tmul a b

end PairingHom

variable [TopologicalSpace G] [IsTopologicalGroup G]

section CupPairing

variable {A B C : Rep.{u} k G} [IsDiscreteRep A] [IsDiscreteRep B] [IsDiscreteRep C] {p q n : ℕ}

def cupPairing (μ : A ⊗ B ⟶ C) (h : p + q = n) :
    cohomology A p →ₗ[k] cohomology B q →ₗ[k] cohomology C n :=
  (cup h).compr₂ (cohomologyMap μ n).hom

theorem cupPairing_apply (μ : A ⊗ B ⟶ C) (h : p + q = n) (x : cohomology A p)
    (y : cohomology B q) : cupPairing μ h x y = cohomologyMap μ n (cup h x y) :=
  rfl

theorem cupPairing_cohomologyπ (μ : A ⊗ B ⟶ C) (h : p + q = n) (x : cocycles A p)
    (y : cocycles B q) :
    cupPairing μ h (cohomologyπ A p x) (cohomologyπ B q y) =
      cohomologyπ C n (HomologicalComplex.cyclesMap (cochainsMap μ) n (cupCocycles h x y)) := by
  rw [cupPairing_apply, cup_cohomologyπ, cohomologyMap_cohomologyπ]

theorem cochainOf_cocycleι_cyclesMap_cupCocycles (μ : A ⊗ B ⟶ C) (h : p + q = n)
    (x : cocycles A p) (y : cocycles B q) (s : Fin n → G) :
    cochainOf C (cocycleι C n
        (HomologicalComplex.cyclesMap (cochainsMap μ) n (cupCocycles h x y))) s =
      μ.hom (cochainOf A (cocycleι A p x) (fun i : Fin p => s ⟨i, by omega⟩) ⊗ₜ[k]
        B.ρ (Fin.partialProd s ⟨p, by omega⟩)
          (cochainOf B (cocycleι B q y) fun j : Fin q => s ⟨p + j, by omega⟩)) := by
  rw [cochainOf_cocycleι_cyclesMap, cocycleι_cupCocycles, cochainOf_cupLocallyConstant]
  rfl

theorem cochainOf_cocycleι_cyclesMap_pairingHom (β : A →ₗ[k] B →ₗ[k] C)
    (hβ : ∀ (g : G) (a : A) (b : B), β (A.ρ g a) (B.ρ g b) = C.ρ g (β a b)) (h : p + q = n)
    (x : cocycles A p) (y : cocycles B q) (s : Fin n → G) :
    cochainOf C (cocycleι C n
        (HomologicalComplex.cyclesMap (cochainsMap (pairingHom β hβ)) n (cupCocycles h x y))) s =
      β (cochainOf A (cocycleι A p x) (fun i : Fin p => s ⟨i, by omega⟩))
        (B.ρ (Fin.partialProd s ⟨p, by omega⟩)
          (cochainOf B (cocycleι B q y) fun j : Fin q => s ⟨p + j, by omega⟩)) := by
  rw [cochainOf_cocycleι_cyclesMap_cupCocycles, pairingHom_tmul]

variable {A' B' C' : Rep.{u} k G} [IsDiscreteRep A'] [IsDiscreteRep B'] [IsDiscreteRep C']

theorem cupPairing_cohomologyMap (μ : A ⊗ B ⟶ C) (f : A' ⟶ A) (g : B' ⟶ B) (h : p + q = n)
    (x : cohomology A' p) (y : cohomology B' q) :
    cupPairing μ h (cohomologyMap f p x) (cohomologyMap g q y) =
      cupPairing ((f ⊗ₘ g) ≫ μ) h x y := by
  rw [cupPairing_apply, cupPairing_apply, ← cohomologyMap_tensorHom_cup, cohomologyMap_comp]
  rfl

theorem cohomologyMap_cupPairing (μ : A ⊗ B ⟶ C) (ν : C ⟶ C') (h : p + q = n)
    (x : cohomology A p) (y : cohomology B q) :
    cohomologyMap ν n (cupPairing μ h x y) = cupPairing (μ ≫ ν) h x y := by
  rw [cupPairing_apply, cupPairing_apply, cohomologyMap_comp]
  rfl

theorem cohomologyRes_cupPairing (μ : A ⊗ B ⟶ C) (S : Subgroup G) (h : p + q = n)
    (x : cohomology A p) (y : cohomology B q) :
    cohomologyRes C S n (cupPairing μ h x y) =
      cupPairing ((resTensorIso S.subtype A B).inv ≫ (Rep.resFunctor S.subtype).map μ) h
        (cohomologyRes A S p x) (cohomologyRes B S q y) := by
  rw [cupPairing_apply, cupPairing_apply, ← cohomologyMap_resTensorIso_cohomologyRes_cup,
    ← ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply, cohomologyMap_comp_cohomologyRes,
    ← cohomologyMap_comp, Iso.hom_inv_id_assoc]
  rfl

end CupPairing

end GroundTheory.ProfCoh
