import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutEXMkTopCut
import Formalism.HermitianCurvature.HermitianCurvatureProofs.LowerParabolicCoordinates

noncomputable section

open Matrix
open scoped ComplexOrder

namespace Formalism.FourierDecayAlt.P.CutEXMT

open Formalism.FourierDecayAlt

variable {n : ℕ}

theorem sum_lt_castLE {j : ℕ} (hj : j ≤ n) (f : Fin n → ℂ) :
    ∑ i : Fin n, (if i.val < j then f i else 0) = ∑ b : Fin j, f (Fin.castLE hj b) := by
  rw [← Finset.sum_filter]
  have e : (Finset.univ.filter fun i : Fin n => i.val < j) = Finset.univ.map (Fin.castLEEmb hj) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map, Fin.castLEEmb_apply]
    constructor
    · intro h; exact ⟨⟨i.val, h⟩, Fin.ext rfl⟩
    · rintro ⟨b, rfl⟩; simp
  rw [e, Finset.sum_map]
  rfl

def gram (Z : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ := Zᴴ * Z

def blkJ (A : Matrix (Fin n) (Fin n) ℂ) (j : Fin n) : Matrix (Fin j) (Fin j) ℂ :=
  Matrix.of fun a b => A (Fin.castLE j.isLt.le a) (Fin.castLE j.isLt.le b)

def colJ (A : Matrix (Fin n) (Fin n) ℂ) (j : Fin n) : Fin j → ℂ := fun a => A (Fin.castLE j.isLt.le a) j

def Wm (Z : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ := Matrix.of fun i j =>
  if h : i.val < j.val then -(((blkJ (gram Z) j)⁻¹ *ᵥ colJ (gram Z) j) ⟨i.val, h⟩) else if i = j then 1 else 0

theorem Wm_ut (Z : Matrix (Fin n) (Fin n) ℂ) : Wm Z ∈ C2.UTset n := by
  refine ⟨fun i j h => ?_, fun i => ?_⟩
  · simp only [Wm, Matrix.of_apply]
    rw [dif_neg (by have : j.val < i.val := h; omega), if_neg (by intro e; rw [e] at h; exact lt_irrefl _ h)]
  · simp [Wm]

theorem mul_col_split (A V : Matrix (Fin n) (Fin n) ℂ) (hV : V ∈ C2.UTset n) (l j : Fin n) :
    (A * V) l j = ∑ b : Fin j, A l (Fin.castLE j.isLt.le b) * V (Fin.castLE j.isLt.le b) j + A l j := by
  rw [Matrix.mul_apply, ← sum_lt_castLE j.isLt.le (fun i => A l i * V i j)]
  have hsplit : ∀ i : Fin n, A l i * V i j = (if i.val < j.val then A l i * V i j else 0) +
      (if i = j then A l j else 0) := by
    intro i
    rcases lt_trichotomy i.val j.val with h | h | h
    · rw [if_pos h, if_neg (by intro e; rw [e] at h; exact lt_irrefl _ h), add_zero]
    · have e : i = j := Fin.ext h
      subst e
      rw [if_neg (lt_irrefl _), if_pos rfl, hV.2, mul_one, zero_add]
    · rw [if_neg (by omega), if_neg (by intro e; rw [e] at h; exact lt_irrefl _ h), hV.1 i j h, mul_zero, add_zero]
  rw [Finset.sum_congr rfl fun i _ => hsplit i, Finset.sum_add_distrib, Finset.sum_ite_eq']
  simp

theorem blk_gram_eq (Z : Matrix (Fin n) (Fin n) ℂ) (j : Fin n) :
    blkJ (gram Z) j = (Matrix.of fun a (b : Fin j) => Z a (Fin.castLE j.isLt.le b))ᴴ *
      Matrix.of fun a (b : Fin j) => Z a (Fin.castLE j.isLt.le b) := by
  ext a b
  simp [blkJ, gram, Matrix.mul_apply, Matrix.conjTranspose_apply]

theorem blk_det_ne {Z : Matrix (Fin n) (Fin n) ℂ} (hZ : Z.det ≠ 0) (j : Fin n) : (blkJ (gram Z) j).det ≠ 0 := by
  rw [blk_gram_eq]
  refine (Matrix.PosDef.det_pos (Matrix.PosDef.conjTranspose_mul_self _ ?_)).ne'
  intro x y hxy
  set ex : (Fin j → ℂ) → Fin n → ℂ := fun x l => if h : l.val < j.val then x ⟨l.val, h⟩ else 0 with hex
  have hm : ∀ x : Fin j → ℂ, (Matrix.of fun a (b : Fin j) => Z a (Fin.castLE j.isLt.le b)) *ᵥ x = Z *ᵥ ex x := by
    intro x
    ext a
    simp only [Matrix.mulVec, dotProduct, Matrix.of_apply]
    set f : Fin n → ℂ := fun l => Z a l * ex x l with hf
    calc ∑ b : Fin j, Z a (Fin.castLE j.isLt.le b) * x b = ∑ b : Fin j, f (Fin.castLE j.isLt.le b) := by
          refine Finset.sum_congr rfl fun b _ => ?_
          simp only [hf, hex, Fin.val_castLE, dif_pos b.isLt]
      _ = ∑ l : Fin n, (if l.val < j.val then f l else 0) := (sum_lt_castLE _ f).symm
      _ = ∑ l : Fin n, f l := by
          refine Finset.sum_congr rfl fun l _ => ?_
          by_cases h : l.val < j.val
          · rw [if_pos h]
          · rw [if_neg h]; simp only [hf, hex, dif_neg h, mul_zero]
  rw [hm, hm] at hxy
  have hinj : Function.Injective (Z *ᵥ ·) := Matrix.mulVec_injective_of_isUnit ((Matrix.isUnit_iff_isUnit_det Z).mpr (isUnit_iff_ne_zero.mpr hZ))
  have := hinj hxy
  funext a
  have h2 := congrFun this (Fin.castLE j.isLt.le a)
  simp only [hex, Fin.val_castLE, dif_pos a.isLt] at h2
  exact h2

theorem Wm_spec {Z : Matrix (Fin n) (Fin n) ℂ} (hZ : Z.det ≠ 0) (l j : Fin n) (hlj : l.val < j.val) :
    (gram Z * Wm Z) l j = 0 := by
  rw [mul_col_split _ _ (Wm_ut Z)]
  have hBc : blkJ (gram Z) j *ᵥ ((blkJ (gram Z) j)⁻¹ *ᵥ colJ (gram Z) j) = colJ (gram Z) j := by
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr (blk_det_ne hZ j)), Matrix.one_mulVec]
  have hrow := congrFun hBc ⟨l.val, hlj⟩
  simp only [Matrix.mulVec, dotProduct, blkJ, colJ, Matrix.of_apply] at hrow
  have hl : Fin.castLE j.isLt.le ⟨l.val, hlj⟩ = l := Fin.ext rfl
  rw [hl] at hrow
  have hW : ∀ b : Fin j, Wm Z (Fin.castLE j.isLt.le b) j =
      -(((blkJ (gram Z) j)⁻¹ *ᵥ colJ (gram Z) j) b) := by
    intro b
    simp only [Wm, Matrix.of_apply, Fin.val_castLE, dif_pos b.isLt, Fin.eta]
  simp only [hW, mul_neg, Finset.sum_neg_distrib]
  rw [show ∑ x : Fin j, gram Z l (Fin.castLE j.isLt.le x) * ((blkJ (gram Z) j)⁻¹ *ᵥ colJ (gram Z) j) x =
      gram Z l j from hrow]
  ring

theorem Wm_unique {Z V : Matrix (Fin n) (Fin n) ℂ} (hZ : Z.det ≠ 0) (hV : V ∈ C2.UTset n)
    (hlow : ∀ l j : Fin n, l.val < j.val → (gram Z * V) l j = 0) : V = Wm Z := by
  ext i j
  rcases lt_trichotomy i.val j.val with h | h | h
  · have hu : IsUnit (blkJ (gram Z) j).det := isUnit_iff_ne_zero.mpr (blk_det_ne hZ j)
    set x : Fin j → ℂ := fun b => V (Fin.castLE j.isLt.le b) j with hx
    have hB : blkJ (gram Z) j *ᵥ x = -colJ (gram Z) j := by
      ext a
      have h0 := hlow (Fin.castLE j.isLt.le a) j (by simp [a.isLt])
      rw [mul_col_split _ _ hV] at h0
      simp only [Matrix.mulVec, dotProduct, blkJ, colJ, Matrix.of_apply, hx, Pi.neg_apply]
      linear_combination h0
    have hx' : x = -((blkJ (gram Z) j)⁻¹ *ᵥ colJ (gram Z) j) := by
      have e : x = (blkJ (gram Z) j)⁻¹ *ᵥ (blkJ (gram Z) j *ᵥ x) := by
        rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hu, Matrix.one_mulVec]
      rw [e, hB, Matrix.mulVec_neg]
    have h1 := congrFun hx' ⟨i.val, h⟩
    simp only [hx, Pi.neg_apply] at h1
    rw [show Fin.castLE j.isLt.le ⟨i.val, h⟩ = i from Fin.ext rfl] at h1
    rw [h1]
    simp only [Wm, Matrix.of_apply, dif_pos h]
  · have e : i = j := Fin.ext h
    subst e
    rw [hV.2, (Wm_ut Z).2]
  · rw [hV.1 i j h, (Wm_ut Z).1 i j h]

theorem gram_mul (Z u : Matrix (Fin n) (Fin n) ℂ) : gram (Z * u) = uᴴ * gram Z * u := by
  simp only [gram, Matrix.conjTranspose_mul, Matrix.mul_assoc]

theorem Wm_mul {Z u : Matrix (Fin n) (Fin n) ℂ} (hZ : Z.det ≠ 0) (hu : u ∈ C2.UTset n) :
    Wm (Z * u) = u⁻¹ * Wm Z := by
  have hZu : (Z * u).det ≠ 0 := by rw [Matrix.det_mul, C2x2.ut_det hu, mul_one]; exact hZ
  refine (Wm_unique hZu (C2x2.ut_mul (C2x2.ut_inv hu) (Wm_ut Z)) ?_).symm
  intro l j hlj
  rw [gram_mul, Matrix.mul_assoc, Matrix.mul_nonsing_inv_cancel_left _ _ (C2x2.ut_unit hu), Matrix.mul_assoc,
    Matrix.mul_apply]
  refine Finset.sum_eq_zero fun i _ => ?_
  by_cases hi : i.val ≤ l.val
  · rw [Wm_spec hZ i j (by omega), mul_zero]
  · rw [Matrix.conjTranspose_apply, hu.1 i l (by show l.val < i.val; omega), star_zero, zero_mul]

def Sm (Z : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ := (Wm Z).adjugate

theorem Sm_eq_inv (Z : Matrix (Fin n) (Fin n) ℂ) : Sm Z = (Wm Z)⁻¹ := by
  rw [Sm, Matrix.inv_def, C2x2.ut_det (Wm_ut Z), Ring.inverse_one, one_smul]

theorem Sm_ut (Z : Matrix (Fin n) (Fin n) ℂ) : Sm Z ∈ C2.UTset n := by
  rw [Sm_eq_inv]; exact C2x2.ut_inv (Wm_ut Z)

theorem Sm_mul {Z u : Matrix (Fin n) (Fin n) ℂ} (hZ : Z.det ≠ 0) (hu : u ∈ C2.UTset n) :
    Sm (Z * u) = Sm Z * u := by
  rw [Sm_eq_inv, Sm_eq_inv, Wm_mul hZ hu, Matrix.mul_inv_rev, Matrix.nonsing_inv_nonsing_inv _ (C2x2.ut_unit hu)]

theorem Wm_mul_Sm (Z : Matrix (Fin n) (Fin n) ℂ) : Wm Z * Sm Z = 1 := by
  rw [Sm_eq_inv]; exact Matrix.mul_nonsing_inv _ (C2x2.ut_unit (Wm_ut Z))

end Formalism.FourierDecayAlt.P.CutEXMT
