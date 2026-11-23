import Mathlib

noncomputable section

open Matrix Polynomial

namespace UpperTheory.V.GradeZeroInterpolatingElement

abbrev M4 (R : Type) : Type := Matrix (Fin 4) (Fin 4) R

def sgn : Fin 4 → ℤ := ![1, 1, -1, -1]

def lamW : Fin 4 → ℤ := ![1, 0, 1, 0]

def muW : Fin 4 → ℤ := ![1, 1, 0, 0]

def wt (i j : Fin 4) : ℤ × ℤ := (lamW i - lamW j, muW i - muW j)

def wAl : ℤ × ℤ := (1, 0)
def wBe : ℤ × ℤ := (-1, 1)
def wPs : ℤ × ℤ := (0, 1)
def wTh : ℤ × ℤ := (1, 1)

def oddRoots : Finset (ℤ × ℤ) := {wAl, -wAl, wBe, -wBe, wTh, -wTh}

def wts : Finset (ℤ × ℤ) := oddRoots ∪ {wPs, -wPs, 0}

theorem wt_mem (i j : Fin 4) : wt i j ∈ wts := by revert i j; decide

theorem wt_rev (i j : Fin 4) : wt j.rev i.rev = wt i j := by revert i j; decide

theorem wt_eq_zero (i j : Fin 4) : wt i j = 0 ↔ i = j := by revert i j; decide

variable {R R' : Type} [CommRing R] [CommRing R']

def adj (X : M4 R) : M4 R := Matrix.of fun i j => (sgn i * sgn j) • X j.rev i.rev

theorem adj_apply (X : M4 R) (i j : Fin 4) : adj X i j = (sgn i * sgn j) • X j.rev i.rev := rfl

def IsGSp (ν : R) (g : M4 R) : Prop := adj g * g = ν • (1 : M4 R)

def sp4 (R : Type) [CommRing R] : Submodule R (M4 R) where
  carrier := {X | adj X = -X}
  zero_mem' := by ext i j; simp [adj_apply]
  add_mem' {a b} ha hb := by
    ext i j
    have h1 := congrFun (congrFun ha i) j
    have h2 := congrFun (congrFun hb i) j
    simp only [adj_apply, Matrix.neg_apply, Matrix.add_apply, smul_add] at *
    rw [h1, h2, neg_add]
  smul_mem' c a ha := by
    ext i j
    have h1 := congrFun (congrFun ha i) j
    simp only [adj_apply, Matrix.neg_apply, Matrix.smul_apply] at *
    rw [smul_comm, h1, smul_neg]

def spW (R : Type) [CommRing R] (w : ℤ × ℤ) : Submodule R (M4 R) :=
  sp4 R ⊓ ⨅ (i : Fin 4) (j : Fin 4) (_ : wt i j ≠ w), LinearMap.ker (Matrix.entryLinearMap R R i j)

def Xm (R : Type) [CommRing R] : M4 R := Matrix.single 2 0 1 + Matrix.single 3 1 1

def IsBlock (X : M4 R) : Prop := ∀ i j, lamW i ≠ lamW j → X i j = 0

def wv (t : Rˣ × Rˣ) (w : ℤ × ℤ) : Rˣ := t.1 ^ w.1 * t.2 ^ w.2

def tconj (t : Rˣ × Rˣ) (X : M4 R) : M4 R := Matrix.of fun i j => (wv t (wt i j) : R) * X i j

def prj (c : Fin 4 → R) (X : M4 R) (i : Fin 4) : M4 R :=
  aeval X (∏ j ∈ Finset.univ.erase i, (Polynomial.X - C (c j)) : R[X])

section Rep

variable {H : Type} [Group H]

def mapRep {n : Type} [Fintype n] [DecidableEq n] (f : R →+* R') (r : H →* Matrix n n R) : H →* Matrix n n R' :=
  (f.mapMatrix : Matrix n n R →+* Matrix n n R').toMonoidHom.comp r

@[simp] theorem mapRep_apply {n : Type} [Fintype n] [DecidableEq n] (f : R →+* R') (r : H →* Matrix n n R) (g : H) (i j : n) :
    mapRep f r g i j = f (r g i j) := rfl

def diagRep (χ : Fin 4 → H →* Rˣ) : H →* M4 R where
  toFun g := Matrix.diagonal fun i => (χ i g : R)
  map_one' := by simp
  map_mul' a b := by simp [Matrix.diagonal_mul_diagonal]

def mono (r : H →* M4 R) (w : ℤ × ℤ) : Set R :=
  {x | ∃ L : List (H × Fin 4 × Fin 4), (L.map fun a => wt a.2.1 a.2.2).sum = w ∧ x = (L.map fun a => r a.1 a.2.1 a.2.2).prod}

def Irr {n : Type} [Fintype n] [DecidableEq n] (r : H →* Matrix n n R) : Prop := Submodule.span R (Set.range r) = ⊤

def Ge (r : H →* M4 R) (i j : Fin 4) : Prop := ∃ g, r g i j ≠ 0

def DiagType (r : H →* M4 R) : Prop := ∀ i j, i ≠ j → Ge r i j → ¬ Ge r j i

def ixA : Fin 2 → Fin 4 := ![0, 2]

def IsConj4 (r r' : H →* M4 R) : Prop := ∃ u : (M4 R)ˣ, ∀ g, r' g = u * r g * (u⁻¹ : (M4 R)ˣ)

structure Ord (I : Subgroup H) (ps : Fin 4 → H → R) (s₀ : H) (r : H →* M4 R) : Prop where
  charpoly : (r s₀).charpoly = ∏ j, (Polynomial.X - C (ps j s₀))
  stable : ∀ g i j, i < j → prj (fun a => ps a s₀) (r s₀) j * r g * prj (fun a => ps a s₀) (r s₀) i = 0
  inert : ∀ s ∈ I, ∀ i, prj (fun a => ps a s₀) (r s₀) i * (r s - ps i s • (1 : M4 R)) * prj (fun a => ps a s₀) (r s₀) i = 0

end Rep

example : IsGSp (1 : R) 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [adj_apply, sgn, Fin.rev, Matrix.one_apply]

example : Xm R ∈ sp4 R := by
  show adj _ = -_
  ext i j
  fin_cases i <;> fin_cases j <;> simp [adj_apply, sgn, Xm, Fin.rev, Matrix.single_apply]

end UpperTheory.V.GradeZeroInterpolatingElement

end
