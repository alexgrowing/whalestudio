import Mathlib
import GroundTheory.AutomorphicForms.FourierWhittaker.IsAddFundamentalDomainImageOfMapVecLattice

open Matrix

namespace GroundTheory.Automorphic

noncomputable section

namespace FourierWhittaker

set_option linter.unusedSectionVars false

abbrev Pos (n : ℕ) : Type := {p : Fin n × Fin n // p.1 < p.2}

variable {n : ℕ} {R : Type*} [CommRing R]

def uN (X : Pos n → R) : Matrix (Fin n) (Fin n) R :=
  Matrix.of fun a b => if h : a < b then X ⟨(a, b), h⟩ else 0

theorem uN_apply (X : Pos n → R) (a b : Fin n) :
    uN X a b = if h : a < b then X ⟨(a, b), h⟩ else 0 := rfl

theorem uN_add (X Y : Pos n → R) : uN (X + Y) = uN X + uN Y := by
  ext a b; simp only [uN_apply, Pi.add_apply, Matrix.add_apply]; split_ifs <;> simp

theorem uN_zero : uN (0 : Pos n → R) = 0 := by
  ext a b; simp only [uN_apply, Pi.zero_apply, Matrix.zero_apply]; split_ifs <;> rfl

theorem uN_neg (X : Pos n → R) : uN (-X) = -uN X := by
  ext a b; simp only [uN_apply, Pi.neg_apply, Matrix.neg_apply]; split_ifs <;> simp

def uMat (X : Pos n → R) : Matrix (Fin n) (Fin n) R := 1 + uN X

theorem uMat_apply (X : Pos n → R) (a b : Fin n) :
    uMat X a b = if a = b then 1 else if h : a < b then X ⟨(a, b), h⟩ else 0 := by
  simp only [uMat, Matrix.add_apply, Matrix.one_apply, uN_apply]
  by_cases h1 : a = b
  · subst h1; simp
  · rw [if_neg h1, if_neg h1, zero_add]

theorem uMat_zero : uMat (0 : Pos n → R) = 1 := by simp [uMat, uN_zero]

theorem det_uMat (X : Pos n → R) : (uMat X).det = 1 := by
  have hT : (uMat X).IsUpperTriangular := by
    intro a b hab
    have hab' : b < a := hab
    rw [uMat_apply, if_neg (ne_of_gt hab'), dif_neg (not_lt.2 hab'.le)]
  rw [Matrix.det_of_isUpperTriangular hT]
  refine Finset.prod_eq_one fun a _ => ?_
  rw [uMat_apply, if_pos rfl]

def uGL (X : Pos n → R) : GL (Fin n) R :=
  ((Matrix.isUnit_iff_isUnit_det (uMat X)).2 (by rw [det_uMat]; exact isUnit_one)).unit

@[simp] theorem coe_uGL (X : Pos n → R) : ((uGL X : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) = uMat X :=
  rfl

theorem uGL_zero : uGL (0 : Pos n → R) = 1 := Units.ext (by simp [uMat_zero])

theorem map_uMat {S : Type*} [CommRing S] (f : R →+* S) (X : Pos n → R) :
    (uMat X).map f = uMat (fun p => f (X p)) := by
  ext a b
  simp only [Matrix.map_apply, uMat_apply]
  split_ifs <;> simp

def colX (k : ℕ) (x : Fin k → R) : Pos n → R :=
  fun p => if h : p.1.2.val = k then x ⟨p.1.1.val, by have := p.2; rw [Fin.lt_def] at this; omega⟩
    else 0

theorem colX_apply (k : ℕ) (x : Fin k → R) (p : Pos n) :
    colX k x p = if h : p.1.2.val = k then
      x ⟨p.1.1.val, by have := p.2; rw [Fin.lt_def] at this; omega⟩ else 0 := rfl

theorem colX_add (k : ℕ) (x y : Fin k → R) : colX (n := n) k (x + y) = colX k x + colX k y := by
  funext p; simp only [colX_apply, Pi.add_apply]; split_ifs <;> simp

theorem colX_zero (k : ℕ) : colX (n := n) k (0 : Fin k → R) = 0 := by
  funext p; simp only [colX_apply, Pi.zero_apply]; split_ifs <;> rfl

theorem colX_neg (k : ℕ) (x : Fin k → R) : colX (n := n) k (-x) = -colX k x := by
  funext p; simp only [colX_apply, Pi.neg_apply]; split_ifs <;> simp

theorem uN_mul_uN_colX {k : ℕ} {Y : Pos n → R} (hY : ∀ p : Pos n, p.1.2.val ≤ k → Y p = 0)
    (x : Fin k → R) : uN Y * uN (colX k x) = 0 := by
  ext a b
  rw [Matrix.mul_apply, Matrix.zero_apply]
  refine Finset.sum_eq_zero fun c _ => ?_
  rw [uN_apply, uN_apply]
  by_cases hcb : c < b
  · rw [dif_pos hcb, colX_apply]
    by_cases hb : b.val = k
    · rw [dif_pos hb]
      by_cases hac : a < c
      · rw [dif_pos hac, hY _ (by rw [Fin.lt_def] at hcb; simp only; omega), zero_mul]
      · rw [dif_neg hac, zero_mul]
    · rw [dif_neg hb, mul_zero]
  · rw [dif_neg hcb, mul_zero]

theorem uMat_mul_uMat_colX {k : ℕ} {Y : Pos n → R} (hY : ∀ p : Pos n, p.1.2.val ≤ k → Y p = 0)
    (x : Fin k → R) : uMat Y * uMat (colX k x) = uMat (Y + colX k x) := by
  rw [uMat, uMat, uMat, mul_add, add_mul, add_mul, one_mul, mul_one, one_mul,
    uN_mul_uN_colX hY, add_zero, uN_add, add_assoc]

def colGL (k : ℕ) (x : Fin k → R) : GL (Fin n) R := uGL (colX k x)

theorem colX_le (k : ℕ) (x : Fin k → R) (p : Pos n) (hp : p.1.2.val ≤ k - 1 ∨ k < p.1.2.val) :
    colX k x p = 0 := by
  rw [colX_apply, dif_neg]
  intro h
  rcases hp with hp | hp
  · have := p.2; rw [Fin.lt_def] at this; omega
  · omega

theorem uN_colX_mul_uN_colX (k : ℕ) (x y : Fin k → R) :
    uN (colX (n := n) k x) * uN (colX k y) = 0 := by
  ext a b
  rw [Matrix.mul_apply, Matrix.zero_apply]
  refine Finset.sum_eq_zero fun c _ => ?_
  simp only [uN_apply, colX_apply]
  split_ifs with h1 h2 h3 h4 <;> first | simp | (rw [Fin.lt_def] at h3; omega)

theorem colGL_add (k : ℕ) (x y : Fin k → R) :
    colGL (n := n) k (x + y) = colGL k x * colGL k y := by
  refine Units.ext ?_
  simp only [colGL, Units.val_mul, coe_uGL, uMat, colX_add, uN_add, mul_add, add_mul, one_mul,
    mul_one, uN_colX_mul_uN_colX, add_zero, add_assoc]

theorem colGL_zero (k : ℕ) : colGL (n := n) (R := R) k 0 = 1 := by
  rw [colGL, colX_zero, uGL_zero]

theorem colGL_neg (k : ℕ) (x : Fin k → R) : colGL (n := n) k (-x) = (colGL k x)⁻¹ := by
  rw [eq_inv_iff_mul_eq_one, ← colGL_add, neg_add_cancel, colGL_zero]

theorem map_colGL {S : Type*} [CommRing S] (f : R →+* S) (k : ℕ) (x : Fin k → R) :
    ((colGL (n := n) k x : GL (Fin n) R) : Matrix (Fin n) (Fin n) R).map f =
      (colGL (n := n) k (fun i => f (x i)) : GL (Fin n) S) := by
  rw [colGL, colGL, coe_uGL, coe_uGL, map_uMat]
  congr 1
  funext p
  simp only [colX_apply]
  split_ifs <;> simp

section Block

variable {j : ℕ}

def splitIdx (hj : j ≤ n) : Fin n ≃ Fin j ⊕ Fin (n - j) :=
  (finCongr (by omega)).trans finSumFinEquiv.symm

theorem splitIdx_of_lt (hj : j ≤ n) (a : Fin n) (ha : a.val < j) :
    splitIdx hj a = Sum.inl ⟨a.val, ha⟩ := by
  have : finCongr (by omega : n = j + (n - j)) a = Fin.castAdd (n - j) ⟨a.val, ha⟩ := Fin.ext rfl
  rw [splitIdx, Equiv.trans_apply, this, finSumFinEquiv_symm_apply_castAdd]

theorem splitIdx_of_ge (hj : j ≤ n) (a : Fin n) (ha : j ≤ a.val) :
    splitIdx hj a = Sum.inr ⟨a.val - j, by omega⟩ := by
  have : finCongr (by omega : n = j + (n - j)) a = Fin.natAdd j ⟨a.val - j, by omega⟩ :=
    Fin.ext (by simp; omega)
  rw [splitIdx, Equiv.trans_apply, this, finSumFinEquiv_symm_apply_natAdd]

def blockMat (hj : j ≤ n) (h : Matrix (Fin j) (Fin j) R) : Matrix (Fin n) (Fin n) R :=
  (Matrix.fromBlocks h 0 0 1).submatrix (splitIdx hj) (splitIdx hj)

theorem blockMat_apply (hj : j ≤ n) (h : Matrix (Fin j) (Fin j) R) (a b : Fin n) :
    blockMat hj h a b = if ha : a.val < j then (if hb : b.val < j then h ⟨a.val, ha⟩ ⟨b.val, hb⟩
      else 0) else (if a = b then 1 else 0) := by
  rw [blockMat, Matrix.submatrix_apply]
  by_cases ha : a.val < j
  · rw [splitIdx_of_lt hj a ha, dif_pos ha]
    by_cases hb : b.val < j
    · rw [splitIdx_of_lt hj b hb, dif_pos hb, Matrix.fromBlocks_apply₁₁]
    · rw [splitIdx_of_ge hj b (not_lt.1 hb), dif_neg hb, Matrix.fromBlocks_apply₁₂,
        Matrix.zero_apply]
  · rw [splitIdx_of_ge hj a (not_lt.1 ha), dif_neg ha]
    by_cases hb : b.val < j
    · rw [splitIdx_of_lt hj b hb, Matrix.fromBlocks_apply₂₁, Matrix.zero_apply, if_neg]
      intro hab; subst hab; exact ha hb
    · rw [splitIdx_of_ge hj b (not_lt.1 hb), Matrix.fromBlocks_apply₂₂, Matrix.one_apply]
      congr 1
      apply propext
      constructor
      · intro h; apply Fin.ext; have := congrArg Fin.val h; simp at this; omega
      · intro h; subst h; rfl

theorem blockMat_mul (hj : j ≤ n) (h₁ h₂ : Matrix (Fin j) (Fin j) R) :
    blockMat hj (h₁ * h₂) = blockMat hj h₁ * blockMat hj h₂ := by
  rw [blockMat, blockMat, blockMat, Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply]
  simp

theorem blockMat_one (hj : j ≤ n) : blockMat hj (1 : Matrix (Fin j) (Fin j) R) = 1 := by
  rw [blockMat, Matrix.fromBlocks_one, Matrix.submatrix_one_equiv]

def blockGL (hj : j ≤ n) : GL (Fin j) R →* GL (Fin n) R :=
  Units.map
    { toFun := blockMat hj
      map_one' := blockMat_one hj
      map_mul' := blockMat_mul hj }

@[simp] theorem coe_blockGL (hj : j ≤ n) (h : GL (Fin j) R) :
    ((blockGL hj h : GL (Fin n) R) : Matrix (Fin n) (Fin n) R) = blockMat hj h := rfl

theorem map_blockMat {S : Type*} [CommRing S] (f : R →+* S) (hj : j ≤ n)
    (h : Matrix (Fin j) (Fin j) R) : (blockMat hj h).map f = blockMat hj (h.map f) := by
  ext a b
  simp only [Matrix.map_apply, blockMat_apply]
  split_ifs <;> simp

theorem blockMat_blockMat {k : ℕ} (hk : k ≤ j) (hj : j ≤ n) (γ : Matrix (Fin k) (Fin k) R) :
    blockMat hj (blockMat hk γ) = blockMat (hk.trans hj) γ := by
  ext a b
  simp only [blockMat_apply]
  split_ifs with h1 h2 h3 h4 h5 h6 <;> first | rfl | omega | simp_all [Fin.ext_iff] | (exfalso; omega)

theorem uMat_colX_eq_blockMat {i : ℕ} (hi : i < j) (hj : j ≤ n) (ξ : Fin i → R) :
    uMat (colX (n := n) i ξ) = blockMat hj (uMat (colX (n := j) i ξ)) := by
  ext a b
  simp only [blockMat_apply, uMat_apply, colX_apply]
  split_ifs <;> (first | rfl | (exfalso; simp only [Fin.ext_iff, Fin.lt_def] at *; omega) | (simp only [Fin.ext_iff, Fin.lt_def] at *; omega) | simp_all [Fin.ext_iff])

def colBlock {j m : ℕ} (x : Fin j → R) : Matrix (Fin j) (Fin m) R :=
  Matrix.of fun i c => if c.val = 0 then x i else 0

theorem uMat_colX_eq_fromBlocks (hj : j < n) (x : Fin j → R) :
    uMat (colX (n := n) j x) = (Matrix.fromBlocks 1 (colBlock (m := n - j) x) 0 1).submatrix
      (splitIdx hj.le) (splitIdx hj.le) := by
  ext a b
  rw [Matrix.submatrix_apply, uMat_apply]
  by_cases ha : a.val < j
  · rw [splitIdx_of_lt hj.le a ha]
    by_cases hb : b.val < j
    · rw [splitIdx_of_lt hj.le b hb, Matrix.fromBlocks_apply₁₁, Matrix.one_apply]
      simp only [colX_apply]
      split_ifs <;> (first | rfl | (exfalso; simp only [Fin.ext_iff, Fin.lt_def] at *; omega) | (simp only [Fin.ext_iff, Fin.lt_def] at *; omega) | simp_all [Fin.ext_iff])
    · rw [splitIdx_of_ge hj.le b (not_lt.1 hb), Matrix.fromBlocks_apply₁₂]
      simp only [colBlock, Matrix.of_apply, colX_apply]
      split_ifs <;> (first | rfl | (exfalso; simp only [Fin.ext_iff, Fin.lt_def] at *; omega) | (simp only [Fin.ext_iff, Fin.lt_def] at *; omega) | simp_all [Fin.ext_iff])
  · rw [splitIdx_of_ge hj.le a (not_lt.1 ha)]
    by_cases hb : b.val < j
    · rw [splitIdx_of_lt hj.le b hb, Matrix.fromBlocks_apply₂₁, Matrix.zero_apply]
      simp only [colX_apply]
      split_ifs <;> (first | rfl | (exfalso; simp only [Fin.ext_iff, Fin.lt_def] at *; omega) | (simp only [Fin.ext_iff, Fin.lt_def] at *; omega) | simp_all [Fin.ext_iff])
    · rw [splitIdx_of_ge hj.le b (not_lt.1 hb), Matrix.fromBlocks_apply₂₂, Matrix.one_apply]
      simp only [colX_apply]
      split_ifs <;> (first | rfl | (exfalso; simp only [Fin.ext_iff, Fin.lt_def] at *; omega) | (simp only [Fin.ext_iff, Fin.lt_def] at *; omega) | simp_all [Fin.ext_iff])

theorem mul_colBlock {m : ℕ} (h : Matrix (Fin j) (Fin j) R) (x : Fin j → R) :
    h * colBlock (m := m) x = colBlock (h.mulVec x) := by
  ext i c
  simp only [Matrix.mul_apply, colBlock, Matrix.of_apply, Matrix.mulVec, dotProduct]
  split_ifs <;> simp

theorem colGL_mul_blockGL (hj : j < n) (h : GL (Fin j) R) (x : Fin j → R) :
    colGL (n := n) j x * blockGL hj.le h =
      blockGL hj.le h * colGL j (((h⁻¹ : GL (Fin j) R) : Matrix (Fin j) (Fin j) R).mulVec x) := by
  refine Units.ext ?_
  simp only [Units.val_mul, colGL, coe_uGL, coe_blockGL]
  rw [uMat_colX_eq_fromBlocks hj, uMat_colX_eq_fromBlocks hj, blockMat, Matrix.submatrix_mul_equiv,
    Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply, mul_colBlock,
    Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]
  simp

theorem blockGL_blockGL {k : ℕ} (hk : k ≤ j) (hj : j ≤ n) (γ : GL (Fin k) R) :
    blockGL hj (blockGL hk γ) = blockGL (hk.trans hj) γ :=
  Units.ext (by
    simp only [coe_blockGL]
    exact blockMat_blockMat hk hj (γ : Matrix (Fin k) (Fin k) R))

theorem colGL_eq_blockGL {i : ℕ} (hi : i < j) (hj : j ≤ n) (ξ : Fin i → R) :
    colGL (n := n) i ξ = blockGL hj (colGL (n := j) i ξ) :=
  Units.ext (by
    simp only [colGL, coe_uGL, coe_blockGL]
    exact uMat_colX_eq_blockMat hi hj ξ)

end Block

end FourierWhittaker

end

end GroundTheory.Automorphic
