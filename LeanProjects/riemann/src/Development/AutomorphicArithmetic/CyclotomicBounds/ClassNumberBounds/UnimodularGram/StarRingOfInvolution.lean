import Mathlib

namespace KStar.Cstarloc

@[reducible] def starRingOfInvolution {R : Type*} [CommRing R] (c : R ≃+* R)
    (hc : Function.Involutive c) : StarRing R where
  star := c
  star_involutive := hc
  star_mul a b := by
    change c (a * b) = c b * c a
    rw [map_mul, mul_comm]
  star_add a b := map_add c a b

structure UnramDatum (R : Type*) [CommRing R] [StarRing R] : Prop where
  trace_one : ∃ e : R, e + star e = 1
  norm_onto : ∀ u : R, IsUnit u → star u = u → ∃ a : R, a * star a = u

variable {R : Type*} [CommRing R] [StarRing R] {M : Type*} [AddCommGroup M] [Module R M]

abbrev Sesq (R : Type*) [CommRing R] [StarRing R] (M : Type*) [AddCommGroup M] [Module R M] :=
  M →ₗ[R] M →ₗ⋆[R] R

def IsHerm (h : Sesq R M) : Prop := ∀ x y, h y x = star (h x y)

def IsUnimod (h : Sesq R M) : Prop := Function.Bijective (h.flip : M → Module.Dual R M)

def gram {ι : Type*} (h : Sesq R M) (b : ι → M) : Matrix ι ι R := Matrix.of fun i j => h (b i) (b j)

def IsOrthonormal {ι : Type*} [DecidableEq ι] (h : Sesq R M) (b : ι → M) : Prop := gram h b = 1

def IsDualPair {ι : Type*} [DecidableEq ι] (h : Sesq R M) (b b' : ι → M) : Prop :=
  ∀ i j, h (b i) (b' j) = if i = j then 1 else 0

def IsHyperbolic {ι : Type*} [DecidableEq ι] (h : Sesq R M) (b : ι ⊕ ι → M) : Prop :=
  gram h b = Matrix.fromBlocks 0 1 1 0

def IsIsotropic (h : Sesq R M) (N : Submodule R M) : Prop := ∀ x ∈ N, ∀ y ∈ N, h x y = 0

def perp (h : Sesq R M) (x : M) : Submodule R M := LinearMap.ker (h.flip x)

def restr (h : Sesq R M) (N : Submodule R M) : Sesq R N := h.domRestrict₁₂ N N

def unitForm (R : Type*) [CommRing R] [StarRing R] : Sesq R R :=
  LinearMap.mk₂'ₛₗ (RingHom.id R) (starRingEnd R) (fun p q => p * star q)
    (fun _ _ _ => add_mul _ _ _) (fun _ _ _ => by simp [mul_assoc])
    (fun _ _ _ => by simp [mul_add]) (fun _ _ _ => by simp [starRingEnd_apply]; ring)

@[simp] theorem unitForm_apply (p q : R) : unitForm R p q = p * star q := rfl

@[simp] theorem restr_apply (h : Sesq R M) (N : Submodule R M) (x y : N) :
    restr h N x y = h x y := rfl

theorem mem_perp (h : Sesq R M) (x y : M) : y ∈ perp h x ↔ h y x = 0 := by
  rw [perp, LinearMap.mem_ker, LinearMap.flip_apply]

end KStar.Cstarloc
