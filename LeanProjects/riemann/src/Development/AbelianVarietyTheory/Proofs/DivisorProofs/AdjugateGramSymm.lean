import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GramPosSemidefOfIntForm

namespace GlobalTheory.CasimirOrder

open Matrix

variable {O : Type} [Ring O]

def form (s : O →+ O) (φ : O →+ ℤ) : LinearMap.BilinForm ℤ O :=
  LinearMap.mk₂ ℤ (fun u v => φ (s u * v))
    (fun u₁ u₂ v => by simp [map_add, add_mul])
    (fun c u v => by rw [map_zsmul, smul_mul_assoc, map_zsmul])
    (fun u v₁ v₂ => by simp [mul_add, map_add])
    (fun c u v => by rw [mul_smul_comm, map_zsmul])

@[simp] theorem form_apply (s : O →+ O) (φ : O →+ ℤ) (u v : O) : form s φ u v = φ (s u * v) := rfl

variable {r : ℕ}

def gram (x : Fin r → O) (s : O →+ O) (φ : O →+ ℤ) : Matrix (Fin r) (Fin r) ℤ :=
  Matrix.of fun i j => φ (s (x i) * x j)

def casimir (x : Fin r → O) (s : O →+ O) (φ : O →+ ℤ) : O :=
  ∑ i, ∑ j, (gram x s φ).adjugate i j • (s (x i) * x j)

theorem det_smul_eq_sum (x : Module.Basis (Fin r) ℤ O) (b : LinearMap.BilinForm ℤ O)
    (hb : ∀ u v, b u v = b v u) (v : O) :
    (Matrix.of fun i j => b (x i) (x j)).det • v =
      ∑ i, ∑ j, ((Matrix.of fun i j => b (x i) (x j)).adjugate i j * b (x i) v) • x j := by
  classical
  set G : Matrix (Fin r) (Fin r) ℤ := Matrix.of fun i j => b (x i) (x j) with hG
  have hGt : Gᵀ = G := by ext i j; simp [hG, hb]
  have hA : ∀ i j, G.adjugate i j = G.adjugate j i := by
    intro i j
    have h := congrArg (fun M : Matrix (Fin r) (Fin r) ℤ => M i j) (adjugate_transpose G)
    rw [hGt] at h
    simpa using h.symm
  have hv : v = ∑ k, x.repr v k • x k := (x.sum_repr v).symm
  have hb' : ∀ i, b (x i) v = ∑ k, G i k * x.repr v k := by
    intro i; conv_lhs => rw [hv]
    rw [map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [LinearMap.map_smul, smul_eq_mul, mul_comm]; rfl
  have key : ∀ j, ∑ i, G.adjugate i j * b (x i) v = G.det * x.repr v j := by
    intro j
    have e : ∑ i, G.adjugate i j * b (x i) v = ∑ k, (G.adjugate * G) j k * x.repr v k := by
      simp_rw [hb', Finset.mul_sum, mul_apply, Finset.sum_mul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun i _ => ?_
      rw [hA]; ring
    rw [e, adjugate_mul]
    simp [Matrix.smul_apply, one_apply]
  rw [Finset.sum_comm]
  simp_rw [← Finset.sum_smul, key]
  conv_lhs => rw [hv]
  rw [Finset.smul_sum]
  exact Finset.sum_congr rfl fun k _ => by rw [smul_smul]

open scoped MatrixOrder in

theorem trace_mul_pos_real {n : ℕ} {P H : Matrix (Fin n) (Fin n) ℝ} (hP : P.PosDef) (hH : H.PosSemidef)
    (h0 : H ≠ 0) : 0 < (P * H).trace := by
  obtain ⟨C, hC, rfl⟩ := CStarAlgebra.isStrictlyPositive_iff_eq_star_mul_self.mp hP.isStrictlyPositive
  have e : (star C * C * H).trace = (C * H * Cᴴ).trace := by
    rw [Matrix.mul_assoc, Matrix.trace_mul_comm]; rfl
  have hs := hH.mul_mul_conjTranspose_same C
  rw [e]
  refine hs.trace_nonneg.lt_of_ne fun h => h0 ?_
  have h1 := hs.trace_eq_zero_iff.1 h.symm
  rwa [show Cᴴ = star C from rfl, hC.star.mul_left_eq_zero, hC.mul_right_eq_zero] at h1

theorem posDef_of_int {n : ℕ} (G : Matrix (Fin n) (Fin n) ℤ) (hs : Gᵀ = G)
    (hp : ∀ v : Fin n → ℤ, v ≠ 0 → 0 < v ⬝ᵥ G *ᵥ v) : (G.map (Int.cast : ℤ → ℝ)).PosDef := by
  classical
  have hsym : ∀ y z, Matrix.toBilin' G y z = Matrix.toBilin' G z y := by
    intro y z
    rw [Matrix.toBilin'_apply', Matrix.toBilin'_apply', Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, hs,
      dotProduct_comm]
  have hnn : ∀ y, 0 ≤ Matrix.toBilin' G y y := by
    intro y
    by_cases hy : y = 0
    · simp [hy]
    · rw [Matrix.toBilin'_apply']; exact (hp y hy).le
  have hpsd : (G.map (Int.cast : ℤ → ℝ)).PosSemidef := by
    have h := GlobalTheory.gram_posSemidef_of_int_form (Matrix.toBilin' G) hsym hnn (fun u => Pi.single u 1)
    convert h using 1
    ext u v
    simp [Matrix.toBilin'_apply']
  rw [hpsd.posDef_iff_isUnit, Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero, ← Int.cast_det]
  intro h
  obtain ⟨z, hz, hGz⟩ := Matrix.exists_mulVec_eq_zero_iff.2 (by exact_mod_cast h)
  have h1 := hp z hz
  rw [hGz, dotProduct_zero] at h1
  exact lt_irrefl _ h1

theorem adjugate_posDef {n : ℕ} {P : Matrix (Fin n) (Fin n) ℝ} (hP : P.PosDef) : P.adjugate.PosDef := by
  have hd := hP.det_pos
  have e : P.adjugate = P.det • P⁻¹ := by
    rw [Matrix.inv_def, smul_smul, Ring.inverse_eq_inv', mul_inv_cancel₀ hd.ne', one_smul]
  rw [e]
  exact hP.inv.smul hd

theorem form_symm {s : O →+ O} {φ : O →+ ℤ} (hs : ∀ a b, s (a * b) = s b * s a) (hss : ∀ a, s (s a) = a)
    (hφs : ∀ a, φ (s a) = φ a) (u v : O) : form s φ u v = form s φ v u := by
  simp only [form_apply]
  rw [← hφs (s u * v), hs, hss]

theorem gram_eq (x : Fin r → O) (s : O →+ O) (φ : O →+ ℤ) :
    gram x s φ = Matrix.of fun i j => form s φ (x i) (x j) := rfl

theorem gram_transpose {x : Fin r → O} {s : O →+ O} {φ : O →+ ℤ} (hs : ∀ a b, s (a * b) = s b * s a)
    (hss : ∀ a, s (s a) = a) (hφs : ∀ a, φ (s a) = φ a) : (gram x s φ)ᵀ = gram x s φ := by
  ext i j
  simp only [transpose_apply, gram_eq, of_apply]
  exact form_symm hs hss hφs _ _

theorem adjugate_gram_symm {x : Fin r → O} {s : O →+ O} {φ : O →+ ℤ} (hs : ∀ a b, s (a * b) = s b * s a)
    (hss : ∀ a, s (s a) = a) (hφs : ∀ a, φ (s a) = φ a) (i j : Fin r) :
    (gram x s φ).adjugate i j = (gram x s φ).adjugate j i := by
  have h := congrArg (fun M : Matrix (Fin r) (Fin r) ℤ => M i j) (adjugate_transpose (gram x s φ))
  rw [gram_transpose hs hss hφs] at h
  simpa using h.symm

theorem casimir_star {x : Fin r → O} {s : O →+ O} {φ : O →+ ℤ} (hs : ∀ a b, s (a * b) = s b * s a)
    (hss : ∀ a, s (s a) = a) (hφs : ∀ a, φ (s a) = φ a) : s (casimir x s φ) = casimir x s φ := by
  unfold casimir
  simp only [map_sum, map_zsmul, hs, hss]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by
    rw [adjugate_gram_symm hs hss hφs]

theorem quad_eq (x : Fin r → O) (b : LinearMap.BilinForm ℤ O) (v : Fin r → ℤ) :
    v ⬝ᵥ (Matrix.of fun i j => b (x i) (x j)) *ᵥ v = b (∑ i, v i • x i) (∑ j, v j • x j) := by
  simp only [dotProduct, mulVec, of_apply, map_sum, LinearMap.sum_apply, LinearMap.map_smul,
    LinearMap.smul_apply, smul_eq_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem posDef_gram (x : Module.Basis (Fin r) ℤ O) (b : LinearMap.BilinForm ℤ O) (hb : ∀ u v, b u v = b v u)
    (hpos : ∀ w, w ≠ 0 → 0 < b w w) :
    ((Matrix.of fun i j => b (x i) (x j)).map (Int.cast : ℤ → ℝ)).PosDef := by
  refine posDef_of_int _ (by ext i j; simp [hb]) fun v hv => ?_
  rw [quad_eq]
  refine hpos _ fun h => hv ?_
  have := (Fintype.linearIndependent_iff.1 x.linearIndependent) v h
  exact funext this

end GlobalTheory.CasimirOrder
