import Mathlib
import GroundTheory.Brauer.TensorSimple
set_option maxSynthPendingDepth 1

namespace GroundTheory.Brauer

open TensorProduct

section Modules

theorem nonempty_linearEquiv_of_finrank_eq {K R : Type*} {M N : Type*} [Field K] [Ring R]
    [Algebra K R] [IsSimpleRing R] [FiniteDimensional K R]
    [AddCommGroup M] [Module K M] [Module R M] [IsScalarTower K R M] [FiniteDimensional K M]
    [AddCommGroup N] [Module K N] [Module R N] [IsScalarTower K R N] [FiniteDimensional K N]
    (h : Module.finrank K M = Module.finrank K N) : Nonempty (M ≃ₗ[R] N) := by
  have : IsArtinianRing R := IsArtinianRing.of_finite K R
  rcases subsingleton_or_nontrivial (M × N) with hMN | hMN
  · have : Subsingleton M := (Prod.fst_surjective (β := N)).subsingleton
    have : Subsingleton N := (Prod.snd_surjective (α := M)).subsingleton
    exact ⟨LinearEquiv.ofSubsingleton M N⟩
  have : Module.Finite R (M × N) := Module.Finite.of_restrictScalars_finite K R _
  have : Module.Finite R M := Module.Finite.of_restrictScalars_finite K R _
  have : Module.Finite R N := Module.Finite.of_restrictScalars_finite K R _
  obtain ⟨k, _, S, hS, -⟩ := (IsSimpleRing.isIsotypic R (M × N)).linearEquiv_fun
  have hT : IsIsotypicOfType R (M × N) S := IsSimpleRing.isIsotypic R (M × N) S
  obtain ⟨m, ⟨eM⟩⟩ := (hT.of_injective (LinearMap.inl R M N) LinearMap.inl_injective).linearEquiv_fun
  obtain ⟨n, ⟨eN⟩⟩ := (hT.of_injective (LinearMap.inr R M N) LinearMap.inr_injective).linearEquiv_fun
  have : Nontrivial S := IsSimpleModule.nontrivial R S
  have : FiniteDimensional K S :=
    FiniteDimensional.of_injective ((Submodule.subtype S).restrictScalars K) Subtype.val_injective
  have hS0 : 0 < Module.finrank K S := Module.finrank_pos
  have hm : Module.finrank K M = m * Module.finrank K S := by
    rw [(eM.restrictScalars K).finrank_eq, Module.finrank_pi_fintype]; simp
  have hn : Module.finrank K N = n * Module.finrank K S := by
    rw [(eN.restrictScalars K).finrank_eq, Module.finrank_pi_fintype]; simp
  obtain rfl : m = n := Nat.eq_of_mul_eq_mul_right hS0 (hm.symm.trans (h.trans hn))
  exact ⟨eM.trans eN.symm⟩

end Modules

namespace SkolemNoether

section Twist

variable {K A B : Type*} [Field K] [Ring A] [Algebra K A] [Ring B] [Algebra K B]

noncomputable def mulRightHom (f : B →ₐ[K] A) : Bᵐᵒᵖ →ₐ[K] Module.End K A where
  toFun b := LinearMap.mulRight K (f b.unop)
  map_one' := by ext; simp
  map_mul' x y := by ext; simp [mul_assoc]
  map_zero' := by ext; simp
  map_add' x y := by ext; simp [mul_add]
  commutes' c := by ext x; simp [Algebra.commutes, Algebra.smul_def]

noncomputable def bimoduleHom (f : B →ₐ[K] A) : A ⊗[K] Bᵐᵒᵖ →ₐ[K] Module.End K A :=
  Algebra.TensorProduct.lift (Algebra.lmul K A) (mulRightHom f) fun a b ↦ by
    ext x; simp [mulRightHom, mul_assoc]

theorem bimoduleHom_tmul (f : B →ₐ[K] A) (a : A) (b : Bᵐᵒᵖ) (x : A) :
    bimoduleHom f (a ⊗ₜ[K] b) x = a * x * f b.unop := by
  simp [bimoduleHom, mulRightHom, mul_assoc]

def Twist (_f : B →ₐ[K] A) : Type _ := A

namespace Twist

variable (f : B →ₐ[K] A)

def of (x : A) : Twist f := x

def val {f : B →ₐ[K] A} (x : Twist f) : A := x

instance : AddCommGroup (Twist f) := inferInstanceAs (AddCommGroup A)

instance : Module K (Twist f) := inferInstanceAs (Module K A)

instance [FiniteDimensional K A] : FiniteDimensional K (Twist f) := inferInstanceAs (FiniteDimensional K A)

noncomputable instance : Module (A ⊗[K] Bᵐᵒᵖ) (Twist f) :=
  letI : Module (A ⊗[K] Bᵐᵒᵖ) A := Module.compHom A (bimoduleHom f).toRingHom
  inferInstanceAs (Module (A ⊗[K] Bᵐᵒᵖ) A)

theorem val_smul (r : A ⊗[K] Bᵐᵒᵖ) (x : Twist f) : (r • x).val = bimoduleHom f r x.val := rfl

instance : IsScalarTower K (A ⊗[K] Bᵐᵒᵖ) (Twist f) :=
  ⟨fun c r x ↦ by
    change bimoduleHom f (c • r) x.val = c • bimoduleHom f r x.val
    rw [map_smul]; rfl⟩

@[simp] theorem val_of (x : A) : (of f x).val = x := rfl

@[simp] theorem of_val (x : Twist f) : of f x.val = x := rfl

variable {f} {g : B →ₐ[K] A}

theorem map_val (φ : Twist f →ₗ[A ⊗[K] Bᵐᵒᵖ] Twist g) (x : A) :
    (φ (of f x)).val = x * (φ (of f 1)).val := by
  have hx : of f x = (x ⊗ₜ[K] (1 : Bᵐᵒᵖ)) • of f 1 := by
    change x = bimoduleHom f (x ⊗ₜ[K] (1 : Bᵐᵒᵖ)) 1
    simp [bimoduleHom_tmul]
  rw [hx, map_smul, val_smul, bimoduleHom_tmul]
  simp

theorem map_val_apply (φ : Twist f →ₗ[A ⊗[K] Bᵐᵒᵖ] Twist g) (b : B) :
    (φ (of f (f b))).val = (φ (of f 1)).val * g b := by
  have hb : of f (f b) = ((1 : A) ⊗ₜ[K] MulOpposite.op b) • of f 1 := by
    change f b = bimoduleHom f ((1 : A) ⊗ₜ[K] MulOpposite.op b) 1
    simp [bimoduleHom_tmul]
  rw [hb, map_smul, val_smul, bimoduleHom_tmul]
  simp

end Twist

end Twist

end SkolemNoether

section SkolemNoether

open SkolemNoether

variable {K A B : Type*} [Field K] [Ring A] [Algebra K A] [Ring B] [Algebra K B]
  [Algebra.IsCentral K A] [IsSimpleRing A] [FiniteDimensional K A]
  [IsSimpleRing B] [FiniteDimensional K B]

theorem exists_unit_conj (f g : B →ₐ[K] A) :
    ∃ a : Aˣ, ∀ x, g x = a * f x * ↑a⁻¹ := by
  obtain ⟨e⟩ := nonempty_linearEquiv_of_finrank_eq (K := K) (R := A ⊗[K] Bᵐᵒᵖ)
    (M := Twist f) (N := Twist g) (by rfl)
  set u := (e (Twist.of f 1)).val with hu
  set v := (e.symm (Twist.of g 1)).val with hv
  have hvu : v * u = 1 := by
    have := Twist.map_val e.toLinearMap v
    simp only [LinearEquiv.coe_coe, hv, Twist.of_val, LinearEquiv.apply_symm_apply] at this
    exact this.symm
  have huv : u * v = 1 := by
    have := Twist.map_val e.symm.toLinearMap u
    simp only [LinearEquiv.coe_coe, hu, Twist.of_val, LinearEquiv.symm_apply_apply] at this
    exact this.symm
  refine ⟨⟨v, u, hvu, huv⟩, fun x ↦ ?_⟩
  have h := (Twist.map_val e.toLinearMap (f x)).symm.trans (Twist.map_val_apply e.toLinearMap x)
  simp only [LinearEquiv.coe_coe, ← hu] at h
  simp only [Units.val_mk, Units.inv_mk, mul_assoc, h, ← mul_assoc v u, hvu, one_mul]

theorem AlgEquiv.exists_unit_conj (σ : A ≃ₐ[K] A) :
    ∃ a : Aˣ, ∀ x, σ x = a * x * ↑a⁻¹ := by
  obtain ⟨a, ha⟩ := GroundTheory.Brauer.exists_unit_conj (AlgHom.id K A) σ.toAlgHom
  exact ⟨a, fun x ↦ by simpa using ha x⟩

end SkolemNoether

end GroundTheory.Brauer
