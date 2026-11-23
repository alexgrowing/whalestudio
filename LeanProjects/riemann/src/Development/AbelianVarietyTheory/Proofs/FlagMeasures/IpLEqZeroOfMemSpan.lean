import Mathlib
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.SameKindIsometric

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas Formalism.REAL

noncomputable section

namespace GlobalTheory.NilCov

variable {n : ℕ} {ε : Fin n → Bool}

def ipL (Y : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ →ₗ[ℝ] ℝ where
  toFun X := ((X * Yᴴ).trace).re
  map_add' X X' := by simp [add_mul]
  map_smul' a X := by simp

theorem ipL_apply (X Y : Matrix (Fin n) (Fin n) ℂ) : ipL Y X = ((X * Yᴴ).trace).re := rfl

theorem ipL_comm (X Y : Matrix (Fin n) (Fin n) ℂ) : ipL Y X = ipL X Y := by
  rw [ipL_apply, ipL_apply]

  have hswap : Y * Xᴴ = (X * Yᴴ)ᴴ := by
    rw [conjTranspose_mul, conjTranspose_conjTranspose]
  rw [hswap, trace_conjTranspose, Complex.star_def, Complex.conj_re]

private theorem Jm_sq_lemma : Jm ε * Jm ε = 1 := by
  rw [Jm, diagonal_mul_diagonal, ← diagonal_one]
  congr 1
  funext a
  by_cases ha : ε a <;> simp [ha]

private theorem Jm_conjTransposeFlagMeasures' : (Jm ε)ᴴ = Jm ε := by
  rw [Jm, diagonal_conjTranspose]
  congr 1
  funext a
  by_cases ha : ε a <;> simp [ha]

private theorem Jm_mul_Jm_mulFlagMeasures (M : Matrix (Fin n) (Fin n) ℂ) : Jm ε * (Jm ε * M) = M := by
  rw [← Matrix.mul_assoc, Jm_sq_lemma, Matrix.one_mul]

theorem inv_eq_neg_of_inG {Y : Matrix (Fin n) (Fin n) ℂ} (h : inG ε Y) : Jm ε * Yᴴ * Jm ε = -Y := by
  have h0 : Yᴴ * Jm ε + Jm ε * Y = 0 := h
  have h1 : Yᴴ * Jm ε = -(Jm ε * Y) := eq_neg_of_add_eq_zero_left h0
  rw [Matrix.mul_assoc, h1, Matrix.mul_neg, Jm_mul_Jm_mulFlagMeasures]

theorem inG_sub_inv (X : Matrix (Fin n) (Fin n) ℂ) : inG ε (X - Jm ε * Xᴴ * Jm ε) := by
  show (X - Jm ε * Xᴴ * Jm ε)ᴴ * Jm ε + Jm ε * (X - Jm ε * Xᴴ * Jm ε) = 0
  simp only [conjTranspose_sub, conjTranspose_mul, conjTranspose_conjTranspose, Jm_conjTransposeFlagMeasures',
    Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_assoc, Jm_sq_lemma, Jm_mul_Jm_mulFlagMeasures, Matrix.mul_one]
  abel

theorem ipL_inv {Y : Matrix (Fin n) (Fin n) ℂ} (h : inG ε Y) (X : Matrix (Fin n) (Fin n) ℂ) :
    ipL Y (Jm ε * Xᴴ * Jm ε) = -ipL Y X := by
  have h0 : Yᴴ * Jm ε + Jm ε * Y = 0 := h
  have h1 : Jm ε * Y = -(Yᴴ * Jm ε) := eq_neg_of_add_eq_zero_right h0

  have hY : Jm ε * Y * Jm ε = -Yᴴ := by
    rw [h1, Matrix.neg_mul, Matrix.mul_assoc, Jm_sq_lemma, Matrix.mul_one]
  have hstar : (Jm ε * Xᴴ * Jm ε)ᴴ = Jm ε * X * Jm ε := by
    simp only [conjTranspose_mul, conjTranspose_conjTranspose, Jm_conjTransposeFlagMeasures', Matrix.mul_assoc]
  have htr : (Y * (Jm ε * X * Jm ε)).trace = -(X * Yᴴ).trace :=
    calc (Y * (Jm ε * X * Jm ε)).trace = ((Y * (Jm ε * X)) * Jm ε).trace := by
          simp only [Matrix.mul_assoc]
      _ = (Jm ε * (Y * (Jm ε * X))).trace := Matrix.trace_mul_comm _ _
      _ = (Jm ε * Y * Jm ε * X).trace := by simp only [Matrix.mul_assoc]
      _ = (-Yᴴ * X).trace := by rw [hY]
      _ = -(X * Yᴴ).trace := by rw [Matrix.neg_mul, Matrix.trace_neg, Matrix.trace_mul_comm]
  rw [ipL_comm, ipL_apply, ipL_apply, hstar, htr, Complex.neg_re]

theorem ipL_sub_inv {Y : Matrix (Fin n) (Fin n) ℂ} (h : inG ε Y) (X : Matrix (Fin n) (Fin n) ℂ) :
    ipL Y (X - Jm ε * Xᴴ * Jm ε) = 2 * ipL Y X := by
  rw [map_sub, ipL_inv h]
  ring

theorem add_inv_eq (g : UJ ε) :
    (uMat g - 1) + Jm ε * (uMat g - 1)ᴴ * Jm ε = -(Jm ε * (uMat g - 1)ᴴ * Jm ε * (uMat g - 1)) := by
  have hg : (uMat g)ᴴ * Jm ε * uMat g = Jm ε := g.2

  have key : Jm ε * (uMat g)ᴴ * Jm ε * uMat g = 1 := by
    calc Jm ε * (uMat g)ᴴ * Jm ε * uMat g = Jm ε * ((uMat g)ᴴ * Jm ε * uMat g) := by
          simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hg, Jm_sq_lemma]
  have e : Jm ε * (uMat g - 1)ᴴ * Jm ε = Jm ε * (uMat g)ᴴ * Jm ε - 1 := by
    rw [conjTranspose_sub, conjTranspose_one, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Jm_sq_lemma]
  rw [e, Matrix.sub_mul, Matrix.mul_sub, key, Matrix.mul_one, Matrix.one_mul]
  abel

variable {d : ℕ} {E : Fin d → Matrix (Fin n) (Fin n) ℂ}

theorem ipL_eq_zero_of_mem_span
    (hE : ∀ i k, ((E i * (E k)ᴴ).trace).re = if i = k then 1 else 0) {s : Set (Fin d)} {i : Fin d}
    (hi : i ∉ s) {X : Matrix (Fin n) (Fin n) ℂ} (hX : X ∈ Submodule.span ℝ (E '' s)) : ipL (E i) X = 0 := by
  have hle : Submodule.span ℝ (E '' s) ≤ LinearMap.ker (ipL (E i)) := by
    rw [Submodule.span_le]
    rintro _ ⟨j, hj, rfl⟩
    have hji : j ≠ i := fun e => hi (e ▸ hj)
    simp [LinearMap.mem_ker, ipL_apply, hE, hji]
  exact hle hX

theorem eq_sum_of_mem_span
    (hE : ∀ i k, ((E i * (E k)ᴴ).trace).re = if i = k then 1 else 0) {X : Matrix (Fin n) (Fin n) ℂ}
    (hX : X ∈ Submodule.span ℝ (Set.range E)) : X = ∑ i, ipL (E i) X • E i := by
  obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).1 hX
  refine Finset.sum_congr rfl fun i _ => ?_
  congr 1

  simp [map_sum, ipL_apply, hE]

theorem ipL_eq_zero_of_mem
    (hE : ∀ i k, ((E i * (E k)ᴴ).trace).re = if i = k then 1 else 0) (hG : ∀ i, inG ε (E i))
    {B : Submodule ℝ (Matrix (Fin n) (Fin n) ℂ)} (hB : ∀ X ∈ B, Jm ε * Xᴴ * Jm ε ∈ B) {s : Set (Fin d)}
    (hs : ∀ X, X ∈ B ∧ inG ε X → X ∈ Submodule.span ℝ (E '' s)) {i : Fin d} (hi : i ∉ s)
    {X : Matrix (Fin n) (Fin n) ℂ} (hX : X ∈ B) : ipL (E i) X = 0 := by
  have hZ : X - Jm ε * Xᴴ * Jm ε ∈ Submodule.span ℝ (E '' s) :=
    hs _ ⟨B.sub_mem hX (hB X hX), inG_sub_inv X⟩
  have h0 := ipL_eq_zero_of_mem_span hE hi hZ
  rw [ipL_sub_inv (hG i)] at h0
  linarith

theorem sub_mem_of_coord_eq {A : ℕ → Submodule ℝ (Matrix (Fin n) (Fin n) ℂ)} {deg : Fin d → ℕ}
    (hmul : ∀ c, ∀ X ∈ A c, ∀ Y ∈ A 0, X * Y ∈ A (c + 1) ∧ Y * X ∈ A (c + 1))
    (hinv : ∀ c, ∀ X ∈ A c, Jm ε * Xᴴ * Jm ε ∈ A c)
    (hE : ∀ i k, ((E i * (E k)ᴴ).trace).re = if i = k then 1 else 0)
    (hsp : ∀ c X, (X ∈ A c ∧ inG ε X) ↔ X ∈ Submodule.span ℝ (E '' {i | c ≤ deg i}))
    {g h : UJ ε} (hg : uMat g - 1 ∈ A 0) (hh : uMat h - 1 ∈ A 0) (c : ℕ)
    (hc : ∀ i, deg i < c → ipL (E i) (uMat g - 1) = ipL (E i) (uMat h - 1)) :
    uMat g - uMat h ∈ A c := by

  have hGi : ∀ i, inG ε (E i) := fun i =>
    ((hsp 0 (E i)).2 (Submodule.subset_span ⟨i, Nat.zero_le _, rfl⟩)).2
  have eX := add_inv_eq g
  have eY := add_inv_eq h
  have hgX : uMat g - 1 ∈ A 0 := hg
  have hhY : uMat h - 1 ∈ A 0 := hh
  revert hc
  generalize uMat g = G at eX eY hgX ⊢
  generalize uMat h = H at eX eY hhY ⊢
  induction c with
  | zero =>
    intro _
    have h0 := (A 0).sub_mem hgX hhY
    rwa [sub_sub_sub_cancel_right] at h0
  | succ c ih =>
    intro hc
    have hD : G - H ∈ A c := ih fun i hi => hc i (Nat.lt_succ_of_lt hi)
    have hθD : Jm ε * (G - H)ᴴ * Jm ε ∈ A c := hinv c _ hD
    have hDXY : G - H = (G - 1) - (H - 1) := (sub_sub_sub_cancel_right G H 1).symm

    have hsym : (G - H) + Jm ε * (G - H)ᴴ * Jm ε ∈ A (c + 1) := by
      have hθ : Jm ε * (G - H)ᴴ * Jm ε = Jm ε * (G - 1)ᴴ * Jm ε - Jm ε * (H - 1)ᴴ * Jm ε := by
        rw [hDXY, conjTranspose_sub, Matrix.mul_sub, Matrix.sub_mul]
      have hprod : (G - H) + Jm ε * (G - H)ᴴ * Jm ε =
          -(Jm ε * (G - 1)ᴴ * Jm ε * (G - H) + Jm ε * (G - H)ᴴ * Jm ε * (H - 1)) := by
        rw [hθ, hDXY, Matrix.mul_sub, Matrix.sub_mul]
        calc (G - 1) - (H - 1) + (Jm ε * (G - 1)ᴴ * Jm ε - Jm ε * (H - 1)ᴴ * Jm ε)
            = ((G - 1) + Jm ε * (G - 1)ᴴ * Jm ε) - ((H - 1) + Jm ε * (H - 1)ᴴ * Jm ε) := by abel
          _ = -(Jm ε * (G - 1)ᴴ * Jm ε * (G - 1)) - -(Jm ε * (H - 1)ᴴ * Jm ε * (H - 1)) := by
            rw [eX, eY]
          _ = _ := by abel
      rw [hprod]
      refine (A (c + 1)).neg_mem ((A (c + 1)).add_mem ?_ ?_)
      · exact (hmul c _ hD _ (hinv 0 _ hgX)).2
      · exact (hmul c _ hθD _ hhY).1

    have hW : (G - H) - Jm ε * (G - H)ᴴ * Jm ε ∈ A (c + 1) := by
      have hWc : (G - H) - Jm ε * (G - H)ᴴ * Jm ε ∈ A c := (A c).sub_mem hD hθD
      have hWsp := (hsp c _).1 ⟨hWc, inG_sub_inv (G - H)⟩
      have hWr : (G - H) - Jm ε * (G - H)ᴴ * Jm ε ∈ Submodule.span ℝ (Set.range E) :=
        Submodule.span_mono (Set.image_subset_range _ _) hWsp
      have hcoord : ∀ i, deg i < c + 1 → ipL (E i) ((G - H) - Jm ε * (G - H)ᴴ * Jm ε) = 0 := by
        intro i hi
        rw [ipL_sub_inv (hGi i), hDXY, map_sub, hc i hi, sub_self, mul_zero]
      have hsum := eq_sum_of_mem_span hE hWr
      have hspan : (G - H) - Jm ε * (G - H)ᴴ * Jm ε ∈ Submodule.span ℝ (E '' {i | c + 1 ≤ deg i}) := by
        rw [hsum]
        refine Submodule.sum_mem _ fun i _ => ?_
        by_cases hi : c + 1 ≤ deg i
        · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, hi, rfl⟩)
        · rw [hcoord i (by omega), zero_smul]
          exact Submodule.zero_mem _
      exact ((hsp (c + 1) _).2 hspan).1
    have h2 : (2 : ℝ) • (G - H) ∈ A (c + 1) := by
      have hs2 := (A (c + 1)).add_mem hsym hW
      convert hs2 using 1
      rw [two_smul]
      abel
    have h1 := (A (c + 1)).smul_mem (1 / 2 : ℝ) h2
    rwa [smul_smul, show (1 / 2 : ℝ) * 2 = 1 by norm_num, one_smul] at h1

end GlobalTheory.NilCov
