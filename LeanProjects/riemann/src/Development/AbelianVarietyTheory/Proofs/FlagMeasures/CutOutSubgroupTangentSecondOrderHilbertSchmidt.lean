import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MeasurableSetHsBall

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.IwConst

namespace GlobalTheory.IwConstApprox

variable {n : ℕ}

theorem nrm_conj_Jm (ε : Fin n → Bool) (X : Matrix (Fin n) (Fin n) ℂ) :
    nrm (Formalism.REAL.Jm ε * X * Formalism.REAL.Jm ε) = nrm X := by

  have hs : ∀ a, ‖(if ε a then (1 : ℂ) else -1)‖ = 1 := fun a => by split_ifs <;> simp
  unfold nrm
  congr 1
  unfold Formalism.REAL.hs Formalism.REAL.Jm
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul, norm_mul, norm_mul, hs, hs, one_mul, mul_one]

theorem nrm_sub_proj_le_sq (n : ℕ) (ε : Fin n → Bool) (S : Set (Formalism.REAL.UJ ε)) (d : ℕ)
    (E : Fin d → Matrix (Fin n) (Fin n) ℂ) (h : IsCut ε S E) (g : Formalism.REAL.UJ ε) (hg : g ∈ S) :
    nrm (uMat g - 1 - cmb E (crd E (uMat g - 1))) ≤ nrm (uMat g - 1) ^ 2 := by

  have hON : IsON E := h.isON
  obtain ⟨H, hH, -⟩ := h.subgroup
  obtain ⟨A, hAmul, -, hspan, hS⟩ := h
  have hJJ : Formalism.REAL.Jm ε * Formalism.REAL.Jm ε = 1 := Formalism.REAL.Jm_mul_self ε
  have hJt : (Formalism.REAL.Jm ε)ᴴ = Formalism.REAL.Jm ε := Formalism.REAL.Jm_conjTranspose ε
  have hJJ' : ∀ M : Matrix (Fin n) (Fin n) ℂ, Formalism.REAL.Jm ε * (Formalism.REAL.Jm ε * M) = M := fun M => by
    rw [← Matrix.mul_assoc, hJJ, Matrix.one_mul]
  have hgU : (uMat g)ᴴ * Formalism.REAL.Jm ε * uMat g = Formalism.REAL.Jm ε := g.2
  have h1 : uMat g⁻¹ * uMat g = 1 := by
    show (((g⁻¹ : Formalism.REAL.UJ ε) : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ) * _ = 1
    rw [Subgroup.coe_inv, Units.inv_mul]
  have h2 : uMat g * uMat g⁻¹ = 1 := by
    show _ * (((g⁻¹ : Formalism.REAL.UJ ε) : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix (Fin n) (Fin n) ℂ) = 1
    rw [Subgroup.coe_inv, Units.mul_inv]
  have hinv : uMat g⁻¹ = Formalism.REAL.Jm ε * (uMat g)ᴴ * Formalism.REAL.Jm ε := by
    calc uMat g⁻¹ = Formalism.REAL.Jm ε * Formalism.REAL.Jm ε * uMat g⁻¹ := by rw [hJJ, Matrix.one_mul]
      _ = Formalism.REAL.Jm ε * ((uMat g)ᴴ * Formalism.REAL.Jm ε * uMat g) * uMat g⁻¹ := by rw [hgU]
      _ = Formalism.REAL.Jm ε * (uMat g)ᴴ * Formalism.REAL.Jm ε * (uMat g * uMat g⁻¹) := by
          simp only [Matrix.mul_assoc]
      _ = Formalism.REAL.Jm ε * (uMat g)ᴴ * Formalism.REAL.Jm ε := by rw [h2, Matrix.mul_one]
  have hgH : g ∈ H := by rw [← SetLike.mem_coe, hH]; exact hg
  have hgi : g⁻¹ ∈ S := by rw [← hH]; exact H.inv_mem hgH
  rw [hS] at hg hgi
  have hXA : uMat g - 1 ∈ A := hg
  have hXsA : uMat g⁻¹ - 1 ∈ A := hgi
  have hXs : Formalism.REAL.Jm ε * (uMat g - 1)ᴴ * Formalism.REAL.Jm ε = uMat g⁻¹ - 1 := by
    rw [hinv]
    simp only [Matrix.conjTranspose_sub, Matrix.conjTranspose_one, Matrix.mul_sub, Matrix.sub_mul,
      Matrix.mul_one, hJJ]
  have key : (uMat g⁻¹ - 1) * (uMat g - 1) = -((uMat g - 1) + (uMat g⁻¹ - 1)) := by
    simp only [Matrix.sub_mul, Matrix.mul_sub, h1, Matrix.mul_one, Matrix.one_mul]
    abel
  have hG : Formalism.REAL.inG ε ((1 / 2 : ℝ) • ((uMat g - 1) - (uMat g⁻¹ - 1))) := by
    rw [← hXs]
    generalize uMat g - 1 = X
    have h0 : (X - Formalism.REAL.Jm ε * Xᴴ * Formalism.REAL.Jm ε)ᴴ * Formalism.REAL.Jm ε +
        Formalism.REAL.Jm ε * (X - Formalism.REAL.Jm ε * Xᴴ * Formalism.REAL.Jm ε) = 0 := by
      simp only [Matrix.conjTranspose_sub, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
        hJt, Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_assoc, hJJ, hJJ', Matrix.mul_one]
      abel
    unfold Formalism.REAL.inG
    rw [Matrix.conjTranspose_smul, star_trivial, Matrix.smul_mul, Matrix.mul_smul, ← smul_add, h0,
      smul_zero]
  have hY : (1 / 2 : ℝ) • ((uMat g - 1) - (uMat g⁻¹ - 1)) ∈ Submodule.span ℝ (Set.range E) :=
    (hspan _).1 ⟨A.smul_mem _ (A.sub_mem hXA hXsA), hG⟩
  have hsq : nrm (uMat g⁻¹ - 1) = nrm (uMat g - 1) := by
    rw [← hXs, nrm_conj_Jm, nrm_conjTranspose]
  calc nrm (uMat g - 1 - cmb E (crd E (uMat g - 1)))
      ≤ nrm (uMat g - 1 - (1 / 2 : ℝ) • ((uMat g - 1) - (uMat g⁻¹ - 1))) := nrm_sub_proj_le hON _ hY
    _ = nrm ((-(1 / 2 : ℝ)) • ((uMat g⁻¹ - 1) * (uMat g - 1))) := by
        rw [key]
        congr 1
        module
    _ = 1 / 2 * nrm ((uMat g⁻¹ - 1) * (uMat g - 1)) := by
        rw [nrm_smul]
        norm_num
    _ ≤ 1 / 2 * (nrm (uMat g⁻¹ - 1) * nrm (uMat g - 1)) := by
        gcongr
        exact nrm_mul_le _ _
    _ ≤ nrm (uMat g - 1) ^ 2 := by
        rw [hsq]
        nlinarith [sq_nonneg (nrm (uMat g - 1)), nrm_nonneg (uMat g - 1)]

end GlobalTheory.IwConstApprox
