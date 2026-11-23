import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TamagawaSpecialUnitary
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.WeightFunctionOnFrames
open NumberField IsDedekindDomain MeasureTheory Matrix GlobalTheory.AdLat GlobalTheory.UCls GlobalTheory.SUVol ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up
open scoped ENNReal

namespace GlobalTheory

theorem skew_transpose_mul_add_mul_conj {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
    (G X : Matrix (Fin r) (Fin r) E)
    (hX : ∀ u w, herm G (X *ᵥ u) w + herm G u (X *ᵥ w) = 0) :
    Xᵀ * G + G * X.map (fun x => cc x) = 0 := by
  ext i j
  have h := hX (Pi.single i 1) (Pi.single j 1)
  have c0 : cc (0 : E) = 0 := map_zero _
  have c1 : cc (1 : E) = 1 := map_one _
  have hc : ∀ b : Fin r, cc (if b = j then (1 : E) else 0) = if b = j then 1 else 0 := by
    intro b; split_ifs <;> simp [c0, c1]
  simp [herm, Matrix.mulVec_single, Pi.single_apply, c0, c1, hc, Matrix.mul_apply] at h ⊢
  exact h

theorem conj_eq_of_skew {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
    (G X : Matrix (Fin r) (Fin r) E) (hG : G.det ≠ 0)
    (hX : ∀ u w, herm G (X *ᵥ u) w + herm G u (X *ᵥ w) = 0) :
    X.map (fun x => cc x) = -(G⁻¹ * Xᵀ * G) := by
  have h := skew_transpose_mul_add_mul_conj G X hX
  have hu : IsUnit G.det := isUnit_iff_ne_zero.mpr hG
  have h2 : G * X.map (fun x => cc x) = -(Xᵀ * G) := eq_neg_of_add_eq_zero_right h
  calc X.map (fun x => cc x) = G⁻¹ * (G * X.map (fun x => cc x)) := by
        rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hu, Matrix.one_mul]
    _ = -(G⁻¹ * Xᵀ * G) := by rw [h2, Matrix.mul_neg, Matrix.mul_assoc]

theorem trace_mul_skew_mem_maximalRealSubfield :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (G : Matrix (Fin r) (Fin r) E) (X Y : Matrix (Fin r) (Fin r) E), (∀ a b, cc (G a b) = G b a) → G.det ≠ 0 → (∀ u w, herm G (X *ᵥ u) w + herm G u (X *ᵥ w) = 0) → (∀ u w, herm G (Y *ᵥ u) w + herm G u (Y *ᵥ w) = 0) → (X * Y).trace ∈ maximalRealSubfield E := by
  intro E _ _ _ r G X Y _ hG hX hY
  have hu : IsUnit G.det := isUnit_iff_ne_zero.mpr hG
  have hXc := conj_eq_of_skew G X hG hX
  have hYc := conj_eq_of_skew G Y hG hY
  rw [← IsCMField.complexConj_eq_self_iff]
  change cc (X * Y).trace = (X * Y).trace
  have hmap : cc (X * Y).trace = ((X * Y).map (fun x => cc x)).trace := by
    simp only [Matrix.trace, Matrix.diag, Matrix.map_apply]
    exact map_sum (IsCMField.complexConj E : E →+* E) _ _
  have hmul : (X * Y).map (fun x => cc x) = X.map (fun x => cc x) * Y.map (fun x => cc x) :=
    Matrix.map_mul (f := ((IsCMField.complexConj E : E ≃ₐ[maximalRealSubfield E] E) : E →+* E))
  rw [hmap, hmul, hXc, hYc, neg_mul_neg]
  have e1 : G⁻¹ * Xᵀ * G * (G⁻¹ * Yᵀ * G) = G⁻¹ * (Xᵀ * Yᵀ * G) := by
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc G G⁻¹, Matrix.mul_nonsing_inv _ hu, Matrix.one_mul]
  rw [e1, Matrix.trace_mul_comm, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hu, Matrix.mul_one,
    ← Matrix.transpose_mul, Matrix.trace_transpose, Matrix.trace_mul_comm]

end GlobalTheory
