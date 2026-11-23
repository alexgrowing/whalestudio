import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmulMemOfIsIntegral

noncomputable section

namespace GlobalTheory.LieDisc.HAdjAlg

open NumberField Matrix GlobalTheory.UCls GlobalTheory.SUVol ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.LieDisc

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem map_mul_cc (A B : Matrix (Fin r) (Fin r) E) : (A * B).map cc = A.map cc * B.map cc :=
  Matrix.map_mul (f := (IsCMField.complexConj E : E →+* E))

theorem map_map_cc (A : Matrix (Fin r) (Fin r) E) : (A.map cc).map cc = A := by
  ext i j; simp [cc_cc]

theorem herm_eq_dot (G : Matrix (Fin r) (Fin r) E) (x y : Fin r → E) :
    herm G x y = x ⬝ᵥ (G *ᵥ fun b => cc (y b)) := by
  simp [herm, dotProduct, mulVec, Finset.mul_sum, mul_assoc]

theorem cc_mulVec (A : Matrix (Fin r) (Fin r) E) (y : Fin r → E) :
    (fun b => cc ((A *ᵥ y) b)) = A.map cc *ᵥ fun b => cc (y b) := by
  ext i; simp [mulVec, dotProduct, cc, map_sum, map_mul]

theorem map_one_cc : (1 : Matrix (Fin r) (Fin r) E).map cc = 1 := by
  ext i j; by_cases h : i = j <;> simp [one_apply, h, cc]

theorem map_smul_cc (c : E) (A : Matrix (Fin r) (Fin r) E) : (c • A).map cc = cc c • A.map cc := by
  ext i j; simp [cc, map_mul]

theorem trace_map_cc (A : Matrix (Fin r) (Fin r) E) : (A.map cc).trace = cc A.trace := by
  simp [Matrix.trace, cc, map_sum]

end GlobalTheory.LieDisc.HAdjAlg

open NumberField Matrix GlobalTheory.UCls GlobalTheory.SUVol ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.LieDisc GlobalTheory.LieDisc.HAdjAlg

theorem GlobalTheory.LieDisc.hAdj_algebra : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (G : Matrix (Fin r) (Fin r) E), (∀ a b, cc (G a b) = G b a) → G.det ≠ 0 → (∀ (Y : Matrix (Fin r) (Fin r) E) (x y : Fin r → E), herm G (Y *ᵥ x) y = herm G x (hAdj G Y *ᵥ y)) ∧ (∀ Y Z : Matrix (Fin r) (Fin r) E, hAdj G (Y * Z) = hAdj G Z * hAdj G Y) ∧ (∀ Y Z : Matrix (Fin r) (Fin r) E, hAdj G (Y + Z) = hAdj G Y + hAdj G Z) ∧ (∀ (c : E) (Y : Matrix (Fin r) (Fin r) E), hAdj G (c • Y) = cc c • hAdj G Y) ∧ hAdj G 1 = 1 ∧ (∀ Y : Matrix (Fin r) (Fin r) E, hAdj G (hAdj G Y) = Y) ∧ (∀ Y : Matrix (Fin r) (Fin r) E, (hAdj G Y).trace = cc Y.trace) ∧ (∀ Y : Matrix (Fin r) (Fin r) E, IsSkew G Y ↔ hAdj G Y = -Y) := by
  intro E _ _ _ r G hG hdet
  have hu : IsUnit G.det := isUnit_iff_ne_zero.mpr hdet
  have hGi : G * G⁻¹ = 1 := mul_nonsing_inv G hu
  have hiG : G⁻¹ * G = 1 := nonsing_inv_mul G hu
  have hGt : G.map cc = Gᵀ := by ext a b; simp [hG]
  have adj1 : ∀ (Y : Matrix (Fin r) (Fin r) E) (x y : Fin r → E),
      herm G (Y *ᵥ x) y = herm G x (hAdj G Y *ᵥ y) := by
    intro Y x y
    rw [herm_eq_dot, herm_eq_dot, cc_mulVec, hAdj, map_map_cc, mulVec_mulVec,
      show G * (G⁻¹ * Yᵀ * G) = Yᵀ * G by rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hGi, Matrix.one_mul],
      ← mulVec_mulVec, dotProduct_mulVec x Yᵀ, vecMul_transpose]
  refine ⟨adj1, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro Y Z
    rw [hAdj, hAdj, hAdj, ← map_mul_cc, transpose_mul]
    congr 1
    simp only [Matrix.mul_assoc, mul_nonsing_inv_cancel_left _ _ hu]
  · intro Y Z
    simp only [hAdj, transpose_add, Matrix.mul_add, Matrix.add_mul]
    ext i j; simp [cc]
  · intro c Y
    rw [hAdj, hAdj, ← map_smul_cc, transpose_smul, Matrix.mul_smul, Matrix.smul_mul]
  · rw [hAdj, transpose_one, Matrix.mul_one, hiG, map_one_cc]
  · intro Y
    have h1 : (G⁻¹).map cc * Gᵀ = 1 := by rw [← hGt, ← map_mul_cc, hiG, map_one_cc]
    have h2 : (G⁻¹)ᵀ * Gᵀ = 1 := by rw [← transpose_mul, hGi, transpose_one]
    rw [hAdj, hAdj, map_mul_cc, map_mul_cc, hGt, ← transpose_map, map_map_cc, transpose_mul, transpose_mul,
      transpose_transpose]
    calc _ = ((G⁻¹).map cc * Gᵀ) * Y * (G⁻¹ᵀ * Gᵀ) := by
          simp only [Matrix.mul_assoc]
      _ = Y := by rw [h1, h2, Matrix.one_mul, Matrix.mul_one]
  · intro Y
    rw [hAdj, trace_map_cc, trace_mul_comm, ← Matrix.mul_assoc, hGi, Matrix.one_mul, trace_transpose]
  · intro Y
    have hadd : ∀ u w, herm G (Y *ᵥ u) w + herm G u (Y *ᵥ w) = herm G u ((hAdj G Y + Y) *ᵥ w) := by
      intro u w
      rw [adj1, herm_eq_dot, herm_eq_dot, herm_eq_dot, ← dotProduct_add, ← mulVec_add]
      congr 2
      ext b; simp [add_mulVec, cc, map_add]
    constructor
    · intro hs
      have hv : ∀ w, (hAdj G Y + Y) *ᵥ w = 0 := by
        intro w
        set v := (hAdj G Y + Y) *ᵥ w
        have h0 : ∀ u, herm G u v = 0 := fun u => by rw [← hadd]; exact hs u w
        have hGv : G *ᵥ (fun b => cc (v b)) = 0 := by
          ext i
          have := h0 (Pi.single i 1)
          rw [herm_eq_dot, single_dotProduct, one_mul] at this
          simpa using this
        have hcv : (fun b => cc (v b)) = 0 := by
          rw [← one_mulVec (fun b => cc (v b)), ← hiG, ← mulVec_mulVec, hGv, mulVec_zero]
        ext b
        have := congrFun hcv b
        simp only [Pi.zero_apply] at this
        rw [← cc_cc (v b), this]; simp [cc]
      have hA : hAdj G Y + Y = 0 := by
        ext i j
        have := congrFun (hv (Pi.single j 1)) i
        simpa [mulVec_single] using this
      exact eq_neg_of_add_eq_zero_left hA
    · intro h u w
      rw [hadd, h, neg_add_cancel, zero_mulVec]
      simp [herm, cc]
