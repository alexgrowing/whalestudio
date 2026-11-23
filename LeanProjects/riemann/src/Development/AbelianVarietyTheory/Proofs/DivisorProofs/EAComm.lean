import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsBaseEqChain
import Development.AbelianVarietyTheory.Definitions.Divisors.FaithfulSMulAlgClosure
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PrismaticDieudonnePerfd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIsoRestrictPushforwardUnit

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry
open GlobalTheory GlobalTheory.QCoh GlobalTheory.Vert GlobalTheory.MixedLocalChains GlobalTheory.ChainPts

namespace GlobalTheory.ChainParts

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {B : Vert.Model O} {Λ : Type} [CommRing Λ]

def eA (M : AM B Λ) {n : ℕ} (c : Fin n → Γ(B.X, ⊤)) (a : Fin n → Λ) : M.V ⟶ M.V :=
  ∑ k, smulHom M.V (c k) ≫ (M.ρ (a k) : M.V ⟶ M.V)

theorem eA_comm {M N : AM B Λ} (f : M ⟶ N) {n : ℕ} (c : Fin n → Γ(B.X, ⊤)) (a : Fin n → Λ) :
    eA M c a ≫ f.hom = f.hom ≫ eA N c a := by
  simp only [eA, Preadditive.sum_comp, Preadditive.comp_sum, Category.assoc]
  refine Finset.sum_congr rfl fun k _ => ?_
  have h1 : (M.ρ (a k) : M.V ⟶ M.V) ≫ f.hom = f.hom ≫ (N.ρ (a k) : N.V ⟶ N.V) := f.comm (a k)
  rw [h1, ← Category.assoc, ← Category.assoc]
  congr 1
  first | exact (smulHom_comp _ _).symm | exact smulHom_comp _ _

def partF {n : ℕ} (c : Fin n → Γ(B.X, ⊤)) (a : Fin n → Λ) : AM B Λ ⥤ B.X.Modules where
  obj M := kernel (𝟙 M.V - eA M c a)
  map f := kernel.map _ _ f.hom f.hom (by
    rw [Preadditive.sub_comp, Preadditive.comp_sub, eA_comm, Category.id_comp, Category.comp_id])
  map_id M := by apply equalizer.hom_ext; simp [kernel.map]
  map_comp f g := by apply equalizer.hom_ext; simp [kernel.map]

instance {n : ℕ} (c : Fin n → Γ(B.X, ⊤)) (a : Fin n → Λ) : (partF c a).Additive :=
  ⟨fun {_ _ _ _} => by
    apply equalizer.hom_ext
    simp only [partF, kernel.map]
    erw [Preadditive.add_comp, kernel.lift_ι, kernel.lift_ι]
    simp⟩

def partι {n : ℕ} (c : Fin n → Γ(B.X, ⊤)) (a : Fin n → Λ) (M : AM B Λ) : (partF c a).obj M ⟶ M.V :=
  kernel.ι (𝟙 M.V - eA M c a)

end GlobalTheory.ChainParts

end
