import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsUnitDetOfIsOrth
open NumberField MeasureTheory Matrix Filter Topology GlobalTheory.SUVol GlobalTheory.RiemConst ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates GlobalTheory.TorusFrame
open scoped ENNReal

namespace GlobalTheory.TorusFrame

open Complex
open scoped ComplexConjugate

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem torusDer_sum_angles (φ : Fin (r - 1) → ℝ) : ∑ a : Fin r, angles φ a = 0 := by
  cases r with
  | zero => simp
  | succ n =>
    rw [Fin.sum_univ_castSucc]
    have h1 : ∀ i : Fin n, angles φ i.castSucc = φ ⟨i, by simp⟩ := by
      intro i; unfold angles; rw [dif_pos (by simp)]; rfl
    have h2 : angles φ (Fin.last n) = -∑ k, φ k := by
      unfold angles; rw [dif_neg (by simp)]
    rw [h2, Finset.sum_congr rfl fun i _ => h1 i]
    rw [add_neg_eq_zero]
    exact Fintype.sum_equiv (finCongr (by simp)) _ _ (fun i => rfl)

theorem torusDer_hermC_dot (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) (u w : Fin r → ℂ) :
    hermC τ G u w = u ⬝ᵥ (G.map τ *ᵥ fun b => conj (w b)) := by
  simp [hermC, dotProduct, mulVec, Finset.mul_sum, mul_assoc]

theorem torusDer_conj_mulVec (Y : Matrix (Fin r) (Fin r) ℂ) (w : Fin r → ℂ) :
    (fun b => conj ((Y *ᵥ w) b)) = Y.map (starRingEnd ℂ) *ᵥ fun b => conj (w b) := by
  ext b; simp [mulVec, dotProduct, map_sum]

theorem torusDer_skew_of_mat (τ : E →+* ℂ) (G : Matrix (Fin r) (Fin r) E) (Y : Matrix (Fin r) (Fin r) ℂ)
    (hK : Yᵀ * G.map τ + G.map τ * Y.map (starRingEnd ℂ) = 0) (u w : Fin r → ℂ) :
    hermC τ G (Y *ᵥ u) w + hermC τ G u (Y *ᵥ w) = 0 := by
  rw [torusDer_hermC_dot, torusDer_hermC_dot, torusDer_conj_mulVec, ← vecMul_transpose, ← dotProduct_mulVec, mulVec_mulVec,
    mulVec_mulVec, ← dotProduct_add, ← add_mulVec, hK, zero_mulVec, dotProduct_zero]

end GlobalTheory.TorusFrame

namespace GlobalTheory.TorusFrame

open Complex
open scoped ComplexConjugate

theorem skewHermitian_of_diagonal_imaginary_frame {r : ℕ} (G M Y : Matrix (Fin r) (Fin r) ℂ) (hu : IsUnit M.det) (d s : Fin r → ℂ)
    (hd : ∀ a, conj (d a) = -d a) (hJ : Mᵀ * G * M.map (starRingEnd ℂ) = diagonal s)
    (hYM : Y * M = M * diagonal d) :
    Yᵀ * G + G * Y.map (starRingEnd ℂ) = 0 := by
  have e1 : Mᵀ * (Yᵀ * G) * M.map (starRingEnd ℂ) = diagonal d * diagonal s := by
    calc Mᵀ * (Yᵀ * G) * M.map (starRingEnd ℂ) = (Y * M)ᵀ * G * M.map (starRingEnd ℂ) := by
          rw [transpose_mul]; simp only [Matrix.mul_assoc]
      _ = diagonal d * diagonal s := by
          rw [hYM, transpose_mul, diagonal_transpose, ← hJ]; simp only [Matrix.mul_assoc]
  have e2 : Mᵀ * (G * Y.map (starRingEnd ℂ)) * M.map (starRingEnd ℂ) =
      diagonal s * (diagonal d).map (starRingEnd ℂ) := by
    calc Mᵀ * (G * Y.map (starRingEnd ℂ)) * M.map (starRingEnd ℂ) = Mᵀ * G * (Y * M).map (starRingEnd ℂ) := by
          rw [Matrix.map_mul]; simp only [Matrix.mul_assoc]
      _ = diagonal s * (diagonal d).map (starRingEnd ℂ) := by
          rw [hYM, Matrix.map_mul, ← hJ]; simp only [Matrix.mul_assoc]
  have h2 : Mᵀ * (Yᵀ * G + G * Y.map (starRingEnd ℂ)) * M.map (starRingEnd ℂ) = 0 := by
    rw [Matrix.mul_add, Matrix.add_mul, e1, e2]
    ext a b
    by_cases h : a = b
    · subst h; simp [diagonal_apply, hd]; ring
    · simp [diagonal_apply, h]
  have hL : (M⁻¹)ᵀ * Mᵀ = 1 := by rw [← transpose_mul, mul_nonsing_inv _ hu, transpose_one]
  have hR : M.map (starRingEnd ℂ) * (M⁻¹).map (starRingEnd ℂ) = 1 := by
    rw [← Matrix.map_mul, mul_nonsing_inv _ hu, Matrix.map_one _ (map_zero _) (map_one _)]
  calc Yᵀ * G + G * Y.map (starRingEnd ℂ)
      = ((M⁻¹)ᵀ * Mᵀ) * (Yᵀ * G + G * Y.map (starRingEnd ℂ)) *
          (M.map (starRingEnd ℂ) * (M⁻¹).map (starRingEnd ℂ)) := by rw [hL, hR, Matrix.one_mul, Matrix.mul_one]
    _ = (M⁻¹)ᵀ * (Mᵀ * (Yᵀ * G + G * Y.map (starRingEnd ℂ)) * M.map (starRingEnd ℂ)) *
          (M⁻¹).map (starRingEnd ℂ) := by simp only [Matrix.mul_assoc]
    _ = 0 := by rw [h2, Matrix.mul_zero, Matrix.zero_mul]

theorem torusDer_skew_diag {r : ℕ} (G M : Matrix (Fin r) (Fin r) ℂ) (hu : IsUnit M.det) (d s : Fin r → ℂ)
    (hd : ∀ a, conj (d a) = -d a) (hJ : Mᵀ * G * M.map (starRingEnd ℂ) = diagonal s) :
    (M * diagonal d * M⁻¹)ᵀ * G + G * (M * diagonal d * M⁻¹).map (starRingEnd ℂ) = 0 :=
  skewHermitian_of_diagonal_imaginary_frame G M _ hu d s hd hJ (by rw [Matrix.mul_assoc, nonsing_inv_mul _ hu, Matrix.mul_one])

theorem torusDer_mem_realLie_and_inFrame : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r)
    (x : Frame X.Ψ r), IsOrth X x → ∀ θ : X.Ψ → Fin (r - 1) → ℝ, torusDer x θ ∈ realLie X.Ψ X.Gm ∧
      ∀ τ a b, inFrame x (torusDer x θ) τ a b = if a = b then Complex.I * (angles (θ τ) a : ℂ) else 0 := by
  intro E _ _ _ r X x hx θ
  have key : ∀ τ : X.Ψ, Matrix.of (torusDer x θ τ) =
      mat x τ * diagonal (fun c => I * (angles (θ τ) c : ℂ)) * (mat x τ)⁻¹ := fun τ => rfl
  refine ⟨?_, fun τ a b => ?_⟩
  · intro τ
    have hu := isUnit_det_of_isOrth hx τ
    refine ⟨?_, fun u w => ?_⟩
    · rw [key, Matrix.trace_mul_comm, ← Matrix.mul_assoc, nonsing_inv_mul _ hu, Matrix.one_mul, trace_diagonal,
        ← Finset.mul_sum, ← ofReal_sum, torusDer_sum_angles, ofReal_zero, mul_zero]
    · rw [key]
      refine torusDer_skew_of_mat τ.1 X.Gm _ ?_ u w
      refine torusDer_skew_diag _ _ hu _ (fun a => ((sgn X.p0 (a : ℕ) : ℝ) : ℂ)) (fun a => ?_) ?_
      · simp
      · rw [← gram_eq]; exact hx τ
  · have hu := isUnit_det_of_isOrth hx τ
    unfold inFrame
    rw [key, show (mat x τ)⁻¹ * (mat x τ * diagonal (fun c => I * (angles (θ τ) c : ℂ)) * (mat x τ)⁻¹) * mat x τ =
        ((mat x τ)⁻¹ * mat x τ) * diagonal (fun c => I * (angles (θ τ) c : ℂ)) * ((mat x τ)⁻¹ * mat x τ) by
        simp only [Matrix.mul_assoc], nonsing_inv_mul _ hu, Matrix.one_mul, Matrix.mul_one, diagonal_apply]

end GlobalTheory.TorusFrame
