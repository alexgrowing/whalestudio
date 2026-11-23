import Mathlib

noncomputable section

open CategoryTheory

namespace UpperTheory.V.KL

section Stab

variable (R : Type) [CommRing R]

def padMat {n m : ℕ} (A : Matrix (Fin n) (Fin n) R) : Matrix (Fin m) (Fin m) R :=
  Matrix.of fun i j =>
    if h : (i : ℕ) < n ∧ (j : ℕ) < n then A ⟨i, h.1⟩ ⟨j, h.2⟩ else if i = j then 1 else 0

theorem padMat_add {n k : ℕ} (A : Matrix (Fin n) (Fin n) R) :
    (padMat R A : Matrix (Fin (n + k)) (Fin (n + k)) R) =
      Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks A 0 0 1) := by
  ext i j
  refine Fin.addCases (fun a => ?_) (fun a => ?_) i <;> refine Fin.addCases (fun c => ?_) (fun c => ?_) j <;>
    simp [padMat, Matrix.one_apply, Fin.ext_iff] <;> omega

def padHom {n m : ℕ} (h : n ≤ m) : Matrix (Fin n) (Fin n) R →* Matrix (Fin m) (Fin m) R where
  toFun := padMat R
  map_one' := by
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
    rw [padMat_add]; simp
  map_mul' A B := by
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
    simp only [padMat_add, Matrix.reindex_apply, Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply]
    simp

def stab (n m : ℕ) (h : n ≤ m) : GL (Fin n) R →* GL (Fin m) R := Units.map (padHom R h)

theorem stab_apply {n m : ℕ} (h : n ≤ m) (g : GL (Fin n) R) (i j : Fin m) :
    (stab R n m h g : Matrix (Fin m) (Fin m) R) i j =
      if h : (i : ℕ) < n ∧ (j : ℕ) < n then (g : Matrix (Fin n) (Fin n) R) ⟨i, h.1⟩ ⟨j, h.2⟩
      else if i = j then 1 else 0 := rfl

instance stab_directedSystem : DirectedSystem (fun n : ℕ => GL (Fin n) R) (fun n m h => stab R n m h) where
  map_self n g := by
    ext i j
    simp [stab_apply]
  map_map k m n hnm hmk g := by
    ext i j
    simp only [stab_apply]
    split_ifs <;> simp_all [Fin.ext_iff] <;> omega

def GLinf : Type := DirectLimit (fun n : ℕ => GL (Fin n) R) (stab R)

instance : Group (GLinf R) := inferInstanceAs (Group (DirectLimit (fun n : ℕ => GL (Fin n) R) (stab R)))

def toGLinf (n : ℕ) : GL (Fin n) R →* GLinf R where
  toFun g := (⟦⟨n, g⟩⟧ : DirectLimit (fun n : ℕ => GL (Fin n) R) (stab R))
  map_one' := (DirectLimit.one_def n).symm
  map_mul' g g' := (DirectLimit.mul_def (G := fun n : ℕ => GL (Fin n) R) (f := stab R) n g g').symm

def Unimodular {n : ℕ} (v : Fin n → R) : Prop := Ideal.span (Set.range v) = ⊤

def StableRangeLe (s : ℕ) : Prop :=
  ∀ n, s ≤ n → ∀ r : Fin (n + 1) → R, Unimodular R r →
    ∃ t : Fin n → R, Unimodular R fun i => r i.castSucc + t i * r (Fin.last n)

end Stab

abbrev grpH (G : Type) [Group G] (n : ℕ) : ModuleCat.{0} ℤ := groupHomology (Rep.trivial ℤ G ℤ) n

def trivHom {G H : Type} [Group G] [Group H] (f : G →* H) :
    Rep.trivial ℤ G ℤ ⟶ Rep.res f (Rep.trivial ℤ H ℤ) := 𝟙 (Rep.trivial ℤ G ℤ)

def grpHMap {G H : Type} [Group G] [Group H] (f : G →* H) (n : ℕ) : grpH G n ⟶ grpH H n :=
  groupHomology.map f (trivHom f) n

end UpperTheory.V.KL

end
