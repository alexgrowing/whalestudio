import Mathlib

noncomputable section

open Matrix

namespace GlobalTheory.PMon

variable {R : Type*} [CommRing R] {a b : Type*} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]

def vecM {S : Type*} (X : Matrix a b S) : a × b → S := fun p => X p.1 p.2

def homUnit (A : GL a R) (B : GL b R) : GL (a × b) R where
  val := Matrix.kroneckerMap (· * ·) (A : Matrix a a R) ((B⁻¹ : GL b R) : Matrix b b R)ᵀ
  inv := Matrix.kroneckerMap (· * ·) ((A⁻¹ : GL a R) : Matrix a a R) (B : Matrix b b R)ᵀ
  val_inv := by
    rw [← Matrix.mul_kronecker_mul, ← Matrix.transpose_mul]
    simp [Matrix.one_kronecker_one]
  inv_val := by
    rw [← Matrix.mul_kronecker_mul, ← Matrix.transpose_mul]
    simp [Matrix.one_kronecker_one]

theorem homUnit_val (A : GL a R) (B : GL b R) :
    ((homUnit A B : GL (a × b) R) : Matrix (a × b) (a × b) R) =
      Matrix.kroneckerMap (· * ·) (A : Matrix a a R) ((B⁻¹ : GL b R) : Matrix b b R)ᵀ := rfl

theorem kronecker_transpose_mulVec {S : Type*} [CommRing S] (A : Matrix a a S) (C : Matrix b b S) (X : Matrix a b S) :
    (Matrix.kroneckerMap (· * ·) A Cᵀ).mulVec (vecM X) = vecM (A * X * C) := by
  funext p
  obtain ⟨i, j⟩ := p
  simp only [vecM, Matrix.mulVec, dotProduct, Matrix.kroneckerMap_apply, Matrix.transpose_apply, Matrix.mul_apply,
    Fintype.sum_prod_type, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun k' _ => ?_
  ring

theorem homUnit_mulVec {S : Type*} [CommRing S] (f : R →+* S) (A : GL a R) (B : GL b R) (X : Matrix a b S) :
    (((homUnit A B : GL (a × b) R) : Matrix (a × b) (a × b) R).map f).mulVec (vecM X) =
      vecM ((A : Matrix a a R).map f * X * ((B⁻¹ : GL b R) : Matrix b b R).map f) := by
  rw [homUnit_val, ← kronecker_transpose_mulVec]
  congr 1
  ext p q
  simp [Matrix.kroneckerMap_apply]

def homRep {G : Type*} [Group G] (ρ₁ : G →* GL a R) (ρ₂ : G →* GL b R) : G →* GL (a × b) R where
  toFun g := homUnit (ρ₁ g) (ρ₂ g)
  map_one' := by
    ext1
    simp [homUnit_val, Matrix.one_kronecker_one]
  map_mul' g h := by
    ext1
    show ((homUnit (ρ₁ (g * h)) (ρ₂ (g * h)) : GL (a × b) R) : Matrix _ _ R) = ((homUnit (ρ₁ g) (ρ₂ g) : GL (a × b) R) : Matrix (a × b) (a × b) R) * ((homUnit (ρ₁ h) (ρ₂ h) : GL (a × b) R) : Matrix (a × b) (a × b) R)
    rw [homUnit_val, homUnit_val, homUnit_val, map_mul, map_mul, _root_.mul_inv_rev, Units.val_mul, Units.val_mul, Matrix.transpose_mul, Matrix.mul_kronecker_mul]

theorem homRep_apply {G : Type*} [Group G] (ρ₁ : G →* GL a R) (ρ₂ : G →* GL b R) (g : G) :
    homRep ρ₁ ρ₂ g = homUnit (ρ₁ g) (ρ₂ g) := rfl

def extCoc {G : Type*} [Group G] (ρ₂ : G →* GL b R) (c : G → Matrix a b R) (g : G) : a × b → R :=
  vecM (c g * (((ρ₂ g)⁻¹ : GL b R) : Matrix b b R))

theorem vecM_injective {S : Type*} : Function.Injective (vecM : Matrix a b S → a × b → S) := by
  intro X Y h
  ext i j
  exact congrFun h (i, j)

end GlobalTheory.PMon
