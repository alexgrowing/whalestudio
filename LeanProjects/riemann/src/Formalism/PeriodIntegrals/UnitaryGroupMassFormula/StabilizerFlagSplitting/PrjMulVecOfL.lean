import Mathlib

open Matrix

noncomputable section

namespace PI.StabSplit.Proj

variable {n ι : Type*} [Fintype n] [DecidableEq n] [Fintype ι] [DecidableEq ι]

def prj (H : Matrix n n ℂ) (Y : Matrix n ι ℂ) : Matrix n n ℂ := Y * (Yᴴ * H * Y)⁻¹ * (Yᴴ * H)

variable (H : Matrix n n ℂ) (Y : Matrix n ι ℂ)

lemma prj_Y (hG : IsUnit (Yᴴ * H * Y).det) : prj H Y * Y = Y := by
  calc prj H Y * Y = Y * ((Yᴴ * H * Y)⁻¹ * (Yᴴ * H * Y)) := by simp only [prj, Matrix.mul_assoc]
    _ = Y := by rw [nonsing_inv_mul _ hG, Matrix.mul_one]

lemma L_prj (hG : IsUnit (Yᴴ * H * Y).det) : (Yᴴ * H) * prj H Y = Yᴴ * H := by
  calc (Yᴴ * H) * prj H Y = ((Yᴴ * H * Y) * (Yᴴ * H * Y)⁻¹) * (Yᴴ * H) := by
        simp only [prj, Matrix.mul_assoc]
    _ = Yᴴ * H := by rw [mul_nonsing_inv _ hG, Matrix.one_mul]

lemma prj_sq (hG : IsUnit (Yᴴ * H * Y).det) : prj H Y * prj H Y = prj H Y := by
  calc prj H Y * prj H Y = (prj H Y * Y) * (Yᴴ * H * Y)⁻¹ * (Yᴴ * H) := by
        simp only [prj, Matrix.mul_assoc]
    _ = prj H Y := by rw [prj_Y H Y hG]; rfl

lemma prj_star (hH : Hᴴ = H) : (prj H Y)ᴴ * H = H * prj H Y := by
  simp only [prj, conjTranspose_mul, conjTranspose_nonsing_inv, hH, conjTranspose_conjTranspose,
    Matrix.mul_assoc]

lemma L_one_sub (hG : IsUnit (Yᴴ * H * Y).det) : (Yᴴ * H) * (1 - prj H Y) = 0 := by
  rw [Matrix.mul_sub, L_prj H Y hG, Matrix.mul_one, sub_self]

lemma prj_mulVec_of_L {v : n → ℂ} (hv : (Yᴴ * H) *ᵥ v = 0) : prj H Y *ᵥ v = 0 := by
  rw [prj, ← Matrix.mulVec_mulVec, hv, Matrix.mulVec_zero]

lemma prj_mul_of_L {m : Type*} [Fintype m] (A : Matrix n m ℂ) (hA : (Yᴴ * H) * A = 0) :
    prj H Y * A = 0 := by
  rw [prj, Matrix.mul_assoc, hA, Matrix.mul_zero]

lemma presM (hG : IsUnit (Yᴴ * H * Y).det) (g : Matrix n n ℂ) (C : Matrix ι ι ℂ) (hC : g * Y = Y * C) :
    (1 - prj H Y) * g * prj H Y = 0 := by
  have : g * prj H Y = Y * C * ((Yᴴ * H * Y)⁻¹ * (Yᴴ * H)) := by
    rw [prj, Matrix.mul_assoc Y, ← Matrix.mul_assoc g, hC]
  rw [Matrix.mul_assoc, this, Matrix.sub_mul, Matrix.one_mul, ← Matrix.mul_assoc (prj H Y),
    ← Matrix.mul_assoc (prj H Y), prj_Y H Y hG, sub_self]

lemma presU (hG : IsUnit (Yᴴ * H * Y).det) (g : Matrix n n ℂ) (hg : gᴴ * H * g = H)
    (hdet : IsUnit g.det) (C : Matrix ι ι ℂ) (hC : g⁻¹ * Y = Y * C) :
    prj H Y * g * (1 - prj H Y) = 0 := by
  have hgs : IsUnit gᴴ.det := by rw [det_conjTranspose]; exact hdet.star
  have hHg : H * g = (g⁻¹)ᴴ * H := by
    rw [conjTranspose_nonsing_inv]
    calc H * g = (gᴴ)⁻¹ * (gᴴ * H * g) := by
          rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, nonsing_inv_mul _ hgs, Matrix.one_mul]
      _ = (gᴴ)⁻¹ * H := by rw [hg]
  have hL : (Yᴴ * H) * g = Cᴴ * (Yᴴ * H) := by
    rw [Matrix.mul_assoc, hHg, ← Matrix.mul_assoc, ← conjTranspose_mul, hC, conjTranspose_mul,
      Matrix.mul_assoc]
  have : (Yᴴ * H) * (g * (1 - prj H Y)) = 0 := by
    rw [← Matrix.mul_assoc, hL, Matrix.mul_assoc, L_one_sub H Y hG, Matrix.mul_zero]
  rw [Matrix.mul_assoc, prj_mul_of_L H Y _ this]

lemma exists_C (A : Matrix n ι ℂ)
    (hA : ∀ j, (fun i => A i j) ∈ Submodule.span ℂ (Set.range fun l => fun i => Y i l)) :
    ∃ C : Matrix ι ι ℂ, A = Y * C := by
  choose c hc using fun j => (Submodule.mem_span_range_iff_exists_fun ℂ).1 (hA j)
  refine ⟨Matrix.of fun l j => c j l, ?_⟩
  ext i j
  have h := congrFun (hc j) i
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at h
  rw [mul_apply, ← h]
  simp [mul_comm]

lemma Y_inj (hG : IsUnit (Yᴴ * H * Y).det) (c : ι → ℂ) (hc : Y *ᵥ c = 0) : c = 0 := by
  have h1 : (Yᴴ * H * Y) *ᵥ c = 0 := by rw [← Matrix.mulVec_mulVec, hc, Matrix.mulVec_zero]
  have h2 := congrArg (fun v => (Yᴴ * H * Y)⁻¹ *ᵥ v) h1
  simpa [Matrix.mulVec_mulVec, nonsing_inv_mul _ hG] using h2

end PI.StabSplit.Proj
