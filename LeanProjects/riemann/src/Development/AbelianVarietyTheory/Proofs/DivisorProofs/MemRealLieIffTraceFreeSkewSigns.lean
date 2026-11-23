import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DetNeZeroOfIsIdent
open NumberField MeasureTheory Matrix GlobalTheory.SUVol ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.CovTop.VolUp GlobalTheory.CovTop.VolUp.FrameBox

private theorem conj_zero_iff' {R : Type} [Ring R] (a b c d S : R) (hba : b * a = 1) (hcd : c * d = 1) :
    S = 0 ↔ a * S * c = 0 := by
  refine ⟨fun h => by simp [h], fun h => ?_⟩
  have e : S = b * (a * S * c) * d := by
    simp only [← mul_assoc, hba, one_mul]; rw [mul_assoc, hcd, mul_one]
  rw [e, h]; simp

private theorem expand' {R : Type} [Ring R] (a b c d y z g : R) (hab : a * b = 1) (hdc : d * c = 1) :
    a * (b * (y * a) * g + g * (c * z * d)) * c = y * (a * g * c) + (a * g * c) * z := by
  have : a * (b * (y * a) * g + g * (c * z * d)) * c = (a * b) * y * (a * g * c) + (a * g * c) * z * (d * c) := by
    simp only [mul_add, add_mul, mul_assoc]
  rw [this, hab, hdc, one_mul, mul_one]

private theorem permJ' {r : ℕ} (p q : ℕ) (e : Fin p ⊕ Fin q ≃ Fin r) :
    (permM e)ᵀ * Formalism.UG.Jpq p q * permM e = diagonal (fun a => if (e.symm a).isLeft then (1:ℂ) else -1) := by
  ext a b
  simp [Matrix.mul_apply, permM, Equiv.apply_eq_iff_eq_symm_apply, diagonal_apply, Formalism.UG.Jpq]
  by_cases hab : a = b
  · subst hab; rw [if_pos rfl]; rcases e.symm a with i | i <;> simp
  · rw [if_neg hab]
    have h := e.symm.injective.ne hab
    revert h
    generalize e.symm a = i
    generalize e.symm b = j
    rcases i with i | i <;> rcases j with j | j <;> intro h <;> simp_all [one_apply]

namespace GlobalTheory.CovTop.VolUp.FrameBox

theorem mem_comap_realLie_iff_skewCond : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (κ : Type)
    (p q : κ → ℕ) (Ψ : Finset (E →+* ℂ)) (G : Matrix (Fin r) (Fin r) E) (x : Frame Ψ r) (σ : κ ≃ Ψ)
    (A : ∀ ρ, Matrix (Fin (p ρ) ⊕ Fin (q ρ)) (Fin r) ℂ) (e : ∀ ρ, Fin (p ρ) ⊕ Fin (q ρ) ≃ Fin r),
    IsIdent p q Ψ G x σ A e → ∀ Y : EuclideanSpace ℂ (Ψ × Fin r × Fin r),
      Y ∈ (realLie Ψ G).comap (fromFrame x) ↔ SkewCond (sgnR σ e) Y := by
  intro E _ _ _ r κ p q Ψ G x σ A e hI Y
  rw [Submodule.mem_comap, GlobalTheory.SUVol.DensOne.mem_realLie_iff]
  refine forall_congr' fun τ => ?_
  have hdet := (det_ne_zero_of_isIdent hI τ).1
  obtain ⟨h1, h2⟩ := hI (σ.symm τ)
  rw [Equiv.apply_symm_apply] at h1 h2
  set P := permM (e (σ.symm τ)) with hP
  set J := Formalism.UG.Jpq (p (σ.symm τ)) (q (σ.symm τ)) with hJdef
  set M := mat x τ with hMdef
  set B := A (σ.symm τ) with hBdef
  set Gt := G.map τ.1 with hGt
  set Yt : Matrix (Fin r) (Fin r) ℂ := Matrix.of fun a b => Y (τ, a, b) with hYt
  have hu : IsUnit M.det := isUnit_iff_ne_zero.mpr hdet
  set N := M⁻¹ with hN
  have hMN : M * N = 1 := Matrix.mul_nonsing_inv M hu
  have hNM : N * M = 1 := Matrix.nonsing_inv_mul M hu
  have hX : Matrix.of (fromFrame x Y τ) = M * Yt * N := rfl
  rw [hX]
  set D : Matrix (Fin r) (Fin r) ℂ := diagonal (fun a => ((sgnR σ e τ a : ℝ) : ℂ)) with hD
  have hPJP : Pᵀ * J * P = D := by
    rw [hP, hJdef, permJ', hD]
    congr 1; funext a; simp only [sgnR]; split_ifs <;> simp
  have hPc : Pᴴ = Pᵀ := by
    ext i j; simp only [hP, permM, conjTranspose_apply, transpose_apply, of_apply]; split_ifs <;> simp
  have hMt : (Mᴴ)ᵀ = M.map (starRingEnd ℂ) := by ext i j; simp
  have hG' : Gt = -(Bᴴ * J * B)ᵀ := by rw [h1, transpose_neg, transpose_transpose, neg_neg]
  have hH : Mᵀ * Gt * M.map (starRingEnd ℂ) = -D := by
    rw [hG', ← hMt, Matrix.mul_neg, Matrix.neg_mul]
    rw [show Mᵀ * (Bᴴ * J * B)ᵀ * (Mᴴ)ᵀ = (Mᴴ * (Bᴴ * J * B) * M)ᵀ by simp only [transpose_mul, Matrix.mul_assoc]]
    have : Mᴴ * (Bᴴ * J * B) * M = Pᵀ * J * P := by
      rw [← hPc, ← h2, conjTranspose_mul]; simp only [Matrix.mul_assoc]
    rw [this, hPJP, hD, diagonal_transpose]
  have hc1 : M.map (starRingEnd ℂ) * N.map (starRingEnd ℂ) = 1 := by
    rw [← Matrix.map_mul, hMN, Matrix.map_one _ (map_zero _) (map_one _)]
  have hc2 : N.map (starRingEnd ℂ) * M.map (starRingEnd ℂ) = 1 := by
    rw [← Matrix.map_mul, hNM, Matrix.map_one _ (map_zero _) (map_one _)]
  have ht1 : Mᵀ * Nᵀ = 1 := by rw [← transpose_mul, hNM, transpose_one]
  have ht2 : Nᵀ * Mᵀ = 1 := by rw [← transpose_mul, hMN, transpose_one]
  have htr : (M * Yt * N).trace = ∑ a, Y (τ, a, a) := by
    rw [trace_mul_comm, ← Matrix.mul_assoc, hNM, Matrix.one_mul]; rfl
  rw [htr, and_comm]
  refine and_congr_right fun _ => ?_
  rw [conj_zero_iff' Mᵀ Nᵀ (M.map (starRingEnd ℂ)) (N.map (starRingEnd ℂ)) _ ht2 hc1]
  rw [transpose_mul, transpose_mul, Matrix.map_mul, Matrix.map_mul]
  rw [expand' _ _ _ _ _ _ _ ht1 hc2, hH]
  rw [Matrix.mul_neg, Matrix.neg_mul, ← neg_add, neg_eq_zero, ← Matrix.ext_iff]
  refine forall_congr' fun a => forall_congr' fun b => ?_
  rw [eq_comm (b := (0 : Matrix (Fin r) (Fin r) ℂ) a b)]
  simp [hD, hYt, Matrix.mul_diagonal, Matrix.diagonal_mul]
  exact eq_comm

end GlobalTheory.CovTop.VolUp.FrameBox
