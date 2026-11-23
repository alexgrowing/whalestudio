import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TamagawaSpecialUnitary
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.WeightFunctionOnFrames
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TangentHaarRealSUOfMap
open NumberField MeasureTheory Matrix GlobalTheory.SUVol ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up
open scoped ComplexConjugate

namespace GlobalTheory.SUVol.FrameSkew

theorem gram_eq_mul {E : Type} [Field E] {r : ℕ} (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E)
    (P : Matrix (Fin r) (Fin r) ℂ) :
    gram τ G P = Pᵀ * G.map τ * P.map (starRingEnd ℂ) := by
  ext a b
  simp only [ReciprocityTheory.ChartRestriction.G.FD.gram, hermC, ReciprocityTheory.ChartRestriction.G.FD.col, Matrix.of_apply, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply,
    Finset.sum_mul]
  rw [Finset.sum_comm]

theorem sgn_mul_self (p0 a : ℕ) : sgn p0 a * sgn p0 a = 1 := by
  unfold sgn; split_ifs <;> norm_num

theorem sgn_ne_zero (p0 a : ℕ) : sgn p0 a ≠ 0 := by
  unfold sgn; split_ifs <;> norm_num

theorem det_ne_of_orth {E : Type} [Field E] {r : ℕ} (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E)
    (P : Matrix (Fin r) (Fin r) ℂ) (p0 : ℕ)
    (h : gram τ G P = Matrix.diagonal fun a : Fin r => ((sgn p0 (a : ℕ) : ℝ) : ℂ)) : P.det ≠ 0 := by
  rw [gram_eq_mul] at h
  have hd := congrArg Matrix.det h
  rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, Matrix.det_diagonal] at hd
  intro h0
  rw [h0, zero_mul, zero_mul] at hd
  exact (Finset.prod_ne_zero_iff.2 fun a _ => by exact_mod_cast sgn_ne_zero p0 a) hd.symm

theorem entries_of_mem {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)
    (x : Frame X.Ψ r) (hx : IsOrth X x) (Y : EuclideanSpace ℂ (X.Ψ × Fin r × Fin r))
    (hY : fromFrame x Y ∈ realLie X.Ψ X.Gm) :
    (∀ τ a b, Y (τ, b, a) = -((sgn X.p0 a * sgn X.p0 b : ℝ) : ℂ) * conj (Y (τ, a, b))) ∧
      ∀ τ, ∑ a, Y (τ, a, a) = 0 := by
  have hL := (GlobalTheory.SUVol.DensOne.mem_realLie_iff X.Ψ X.Gm (fromFrame x Y)).1 hY
  have hP : ∀ τ, (mat x τ).det ≠ 0 := fun τ => det_ne_of_orth τ.1 X.Gm (mat x τ) X.p0 (hx τ)
  constructor
  · intro τ a b
    set P := mat x τ with hPdef
    set Ym : Matrix (Fin r) (Fin r) ℂ := Matrix.of fun a b => Y (τ, a, b) with hYm
    set Gt := X.Gm.map τ.1
    set D : Matrix (Fin r) (Fin r) ℂ := Matrix.diagonal fun a : Fin r => ((sgn X.p0 (a : ℕ) : ℝ) : ℂ) with hD
    have hO : Pᵀ * Gt * P.map (starRingEnd ℂ) = D := by rw [← gram_eq_mul]; exact hx τ
    have hu : IsUnit P.det := isUnit_iff_ne_zero.2 (hP τ)
    have hinv : P⁻¹ * P = 1 := Matrix.nonsing_inv_mul P hu
    have hinvT : Pᵀ * (P⁻¹)ᵀ = 1 := by rw [← Matrix.transpose_mul, hinv, Matrix.transpose_one]
    have hinvC : (P⁻¹).map (starRingEnd ℂ) * P.map (starRingEnd ℂ) = 1 := by
      rw [← Matrix.map_mul, hinv, Matrix.map_one _ (map_zero _) (map_one _)]
    have hM : Matrix.of (fromFrame x Y τ) = P * Ym * P⁻¹ := rfl
    have h1 := (hL τ).1
    rw [hM] at h1
    have h2 : Pᵀ * ((P * Ym * P⁻¹)ᵀ * Gt + Gt * (P * Ym * P⁻¹).map (starRingEnd ℂ)) * P.map (starRingEnd ℂ) = 0 := by
      rw [h1, Matrix.mul_zero, Matrix.zero_mul]
    have h3 : Ymᵀ * D + D * Ym.map (starRingEnd ℂ) = 0 := by
      rw [← h2, ← hO]
      simp only [Matrix.transpose_mul, Matrix.map_mul, Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc]
      congr 1
      · rw [← Matrix.mul_assoc Pᵀ P⁻¹ᵀ, hinvT, Matrix.one_mul]
      · rw [hinvC, Matrix.mul_one]
    have h4 := congrFun (congrFun h3 a) b
    simp only [hD, Matrix.add_apply, Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.transpose_apply,
      Matrix.map_apply, hYm, Matrix.of_apply, Matrix.zero_apply] at h4
    have hs : ((sgn X.p0 (b : ℕ) : ℝ) : ℂ) * ((sgn X.p0 (b : ℕ) : ℝ) : ℂ) = 1 := by
      exact_mod_cast sgn_mul_self X.p0 b
    push_cast
    linear_combination (((sgn X.p0 (b : ℕ) : ℝ) : ℂ)) * h4 - Y (τ, b, a) * hs
  · intro τ
    have h1 := (hL τ).2
    have hM : Matrix.of (fromFrame x Y τ) = mat x τ * Matrix.of (fun a b => Y (τ, a, b)) * (mat x τ)⁻¹ := rfl
    rw [hM, Matrix.trace_mul_comm, ← Matrix.mul_assoc,
      Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.2 (hP τ)), Matrix.one_mul] at h1
    simpa [Matrix.trace] using h1

end GlobalTheory.SUVol.FrameSkew
