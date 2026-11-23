import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.InterPolyProdSum

set_option autoImplicit false

noncomputable section

open MvPolynomial GlobalTheory.FlagBundle
open scoped Matrix

namespace GlobalTheory.GoodMetric

variable {ι : Type} {m : ι → ℕ}

abbrev EntIx (m : ι → ℕ) : Type := Σ τ, Fin (m τ) × Fin (m τ)

def evEnt {M : ℕ} (P : Matrix (Fin M) (Fin M) (MvPolynomial (EntIx m) ℤ)) {R : Type} [CommRing R] (A : Mat m R) :
    Matrix (Fin M) (Fin M) R :=
  P.map (aeval fun v : EntIx m => A v.1 v.2.1 v.2.2)

structure PolyRep (m : ι → ℕ) : Type where

  M : ℕ

  ent : Matrix (Fin M) (Fin M) (MvPolynomial (EntIx m) ℤ)
  one : ∀ (R : Type) [CommRing R], evEnt ent (1 : Mat m R) = 1
  mul : ∀ (R : Type) [CommRing R] (A B : Mat m R), evEnt ent (A * B) = evEnt ent A * evEnt ent B
  transp : ∀ (R : Type) [CommRing R] (A : Mat m R), evEnt ent (fun τ => (A τ)ᵀ) = (evEnt ent A)ᵀ

namespace PolyRep

def ev (ρ : PolyRep m) {R : Type} [CommRing R] (A : Mat m R) : Matrix (Fin ρ.M) (Fin ρ.M) R := evEnt ρ.ent A

def lie [Fintype ι] (ρ : PolyRep m) {R : Type} [CommRing R] (A : Mat m R) : Matrix (Fin ρ.M) (Fin ρ.M) R :=
  Matrix.of fun i j => ∑ v : EntIx m,
    aeval (fun w : EntIx m => (1 : Mat m R) w.1 w.2.1 w.2.2) (pderiv v (ρ.ent i j)) * A v.1 v.2.1 v.2.2

def proj (m : ι → ℕ) (τ : ι) : PolyRep m where
  M := m τ
  ent := Matrix.of fun i j => X ⟨τ, (i, j)⟩
  one R _ := by ext i j; simp [evEnt]
  mul R _ A B := by ext i j; simp [evEnt, Matrix.mul_apply]
  transp R _ A := by ext i j; simp [evEnt]

theorem ev_proj (τ : ι) {R : Type} [CommRing R] (A : Mat m R) : (proj m τ).ev A = A τ := by
  ext i j
  exact aeval_X (R := ℤ) (fun v : EntIx m => A v.1 v.2.1 v.2.2) ⟨τ, (i, j)⟩

end PolyRep

end GlobalTheory.GoodMetric

end
