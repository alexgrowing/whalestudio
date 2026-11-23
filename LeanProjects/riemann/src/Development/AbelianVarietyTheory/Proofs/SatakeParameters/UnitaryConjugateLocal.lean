import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.LandherrCSA

noncomputable section
namespace GlobalTheory.UStab
open GlobalTheory.HermCSA
open scoped TensorProduct

section Ring
variable {R : Type} [Ring R]

def IsUn (σ : R →+ R) (g : R) : Prop := σ g * g = 1

def SConj (γ δ : R) : Prop := ∃ x : Rˣ, δ = x * γ * ↑x⁻¹

def UConj (σ : R →+ R) (δ δ' : R) : Prop := ∃ g : Rˣ, σ g * g = 1 ∧ δ' = g * δ * ↑g⁻¹

end Ring

def IsRegElt (F : Type) {C : Type} [Field F] [Ring C] [Algebra F C] (γ : C) : Prop :=
  Module.finrank F (Algebra.adjoin F {γ}) ^ 2 = Module.finrank F C

abbrev sK {C : Type} [Ring C] (s : C →+ C) (K : Type) [CommRing K] : K ⊗[ℤ] C →+ K ⊗[ℤ] C :=
  (ext C K s).toAddMonoidHom

section Ext
variable {C : Type} [Ring C] (s : C →+ C) (K : Type) [CommRing K]

@[simp] theorem sK_tmul (k : K) (c : C) : sK s K (k ⊗ₜ c) = k ⊗ₜ s c := rfl

theorem sK_mul (hm : ∀ x y, s (x * y) = s y * s x) (u v : K ⊗[ℤ] C) :
    sK s K (u * v) = sK s K v * sK s K u := by
  induction u using TensorProduct.induction_on with
  | zero => simp
  | tmul k c =>
    induction v using TensorProduct.induction_on with
    | zero => simp
    | tmul k' c' => simp [Algebra.TensorProduct.tmul_mul_tmul, hm, mul_comm]
    | add v w hv hw => rw [mul_add, map_add, map_add, hv, hw, add_mul]
  | add u w hu hw => rw [add_mul, map_add, map_add, hu, hw, mul_add]

theorem sK_sK (hi : ∀ x, s (s x) = x) (u : K ⊗[ℤ] C) : sK s K (sK s K u) = u := by
  induction u using TensorProduct.induction_on with
  | zero => simp
  | tmul k c => simp [hi]
  | add u w hu hw => rw [map_add, map_add, hu, hw]

end Ext

section Grp
variable {G : Type} [Group G]

end Grp

section Alg
variable {R : Type} [Ring R] (σ : R →+ R)

theorem σ_one (hm : ∀ x y, σ (x * y) = σ y * σ x) (hi : ∀ x, σ (σ x) = x) : σ 1 = 1 := by
  have h := hm (σ 1) 1
  rw [mul_one, hi] at h
  simpa using h.symm

def σU (hm : ∀ x y, σ (x * y) = σ y * σ x) (hi : ∀ x, σ (σ x) = x) (u : Rˣ) : Rˣ :=
  ⟨σ u, σ ↑u⁻¹, by rw [← hm, Units.inv_mul, σ_one σ hm hi], by rw [← hm, Units.mul_inv, σ_one σ hm hi]⟩

theorem σU_val (hm : ∀ x y, σ (x * y) = σ y * σ x) (hi : ∀ x, σ (σ x) = x) (u : Rˣ) :
    σ (u : R) = (σU σ hm hi u : R) := rfl

theorem σU_inv_val (hm : ∀ x y, σ (x * y) = σ y * σ x) (hi : ∀ x, σ (σ x) = x) (u : Rˣ) :
    σ (↑u⁻¹ : R) = ↑(σU σ hm hi u)⁻¹ := rfl

theorem σU_mul (hm : ∀ x y, σ (x * y) = σ y * σ x) (hi : ∀ x, σ (σ x) = x) (u v : Rˣ) :
    σU σ hm hi (u * v) = σU σ hm hi v * σU σ hm hi u := by
  ext; simp only [Units.val_mul, ← σU_val σ hm hi, hm]

theorem σU_inv (hm : ∀ x y, σ (x * y) = σ y * σ x) (hi : ∀ x, σ (σ x) = x) (u : Rˣ) :
    σU σ hm hi u⁻¹ = (σU σ hm hi u)⁻¹ := by
  ext; rfl

end Alg

section Alg2
variable {R : Type} [Ring R] (σ : R →+ R) (hm : ∀ x y, σ (x * y) = σ y * σ x) (hi : ∀ x, σ (σ x) = x)
include hm hi

end Alg2

end GlobalTheory.UStab

namespace GlobalTheory.UStab
open GlobalTheory.HermCSA NumberField
open scoped TensorProduct

section Loc
variable {C : Type} [Ring C] (s : C →+ C) (hm : ∀ x y, s (x * y) = s y * s x) (hi : ∀ x, s (s x) = x)
  (K : Type) [CommRing K]

def uK (x : Cˣ) : (K ⊗[ℤ] C)ˣ :=
  Units.map (Algebra.TensorProduct.includeRight : C →ₐ[ℤ] K ⊗[ℤ] C).toMonoidHom x

theorem uK_val (x : Cˣ) : ((uK K x : (K ⊗[ℤ] C)ˣ) : K ⊗[ℤ] C) = (1 : K) ⊗ₜ (x : C) := rfl

include hm hi

theorem σU_uK (x : Cˣ) :
    σU (sK s K) (sK_mul s K hm) (sK_sK s K hi) (uK K x) = uK K (σU s hm hi x) := by
  ext; rfl

theorem hv (x : Cˣ) : ((σU (sK s K) (sK_mul s K hm) (sK_sK s K hi) (uK K x) * uK K x : (K ⊗[ℤ] C)ˣ) : K ⊗[ℤ] C)
    = (1 : K) ⊗ₜ (s x * (x : C)) := by
  rw [σU_uK s hm hi, Units.val_mul, uK_val, uK_val, Algebra.TensorProduct.tmul_mul_tmul, one_mul]; rfl

end Loc
end GlobalTheory.UStab

namespace GlobalTheory.UStab
open GlobalTheory.HermCSA NumberField
open scoped TensorProduct

section Loc2
variable {C : Type} [Ring C] (s : C →+ C) (hm : ∀ x y, s (x * y) = s y * s x) (hi : ∀ x, s (s x) = x)
  (K : Type) [CommRing K]
include hm hi

end Loc2
end GlobalTheory.UStab
