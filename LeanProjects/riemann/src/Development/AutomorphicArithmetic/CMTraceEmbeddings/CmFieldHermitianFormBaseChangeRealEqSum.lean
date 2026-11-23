import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.OrientEv

open NumberField Matrix GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.LKTrip GlobalTheory.LKGeo UpperTheory.Gal.W2.Seed UpperTheory.Gal.W2.Seed.Ori
open scoped TensorProduct

private noncomputable def R {K : Type} [Fintype K] (c u v : K → ℂ) : ℝ :=
  ∑ k, 2 * (c k * u k * (starRingEnd ℂ) (v k)).re

private theorem R_add_l {K : Type} [Fintype K] (c u u' v : K → ℂ) :
    R c (u + u') v = R c u v + R c u' v := by
  unfold R
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [Pi.add_apply, mul_add, add_mul, Complex.add_re]

private theorem R_add_r {K : Type} [Fintype K] (c u v v' : K → ℂ) :
    R c u (v + v') = R c u v + R c u v' := by
  unfold R
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [Pi.add_apply, map_add, mul_add, add_mul, Complex.add_re]

private theorem R_smul_l {K : Type} [Fintype K] (c u v : K → ℂ) (r : ℝ) :
    R c (r • u) v = r * R c u v := by
  simp only [R, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  have h : c k * (r • u) k * (starRingEnd ℂ) (v k) = (r : ℂ) * (c k * u k * (starRingEnd ℂ) (v k)) := by
    simp only [Pi.smul_apply, Complex.real_smul]; ring
  rw [h, Complex.re_ofReal_mul]; ring

private theorem R_smul_r {K : Type} [Fintype K] (c u v : K → ℂ) (r : ℝ) :
    R c u (r • v) = r * R c u v := by
  simp only [R, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  have h : c k * u k * (starRingEnd ℂ) ((r • v) k) = (r : ℂ) * (c k * u k * (starRingEnd ℂ) (v k)) := by
    simp only [Pi.smul_apply, Complex.real_smul, map_mul, Complex.conj_ofReal]; ring
  rw [h, Complex.re_ofReal_mul]; ring

private theorem core0 (hT : TraceType) {E : Type} [Field E] [NumberField E] [IsCMField E] (A : Arith E) (n : ℕ)
    (a b : Fin n → 𝓞 E) :
    ((A.EF n a b : ℤ) : ℝ) = ∑ k : Phi A × Fin n, 2 * (k.1.1 A.δ * k.1.1 (A.hd n k.2 : E) * k.1.1 (a k.2 : E) *
      (starRingEnd ℂ) (k.1.1 (b k.2 : E))).re := by
  rw [Arith.EF_apply, ← Rat.cast_intCast, Arith.trd_spec, (hT E A).1, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun τ _ => ?_
  rw [← Finset.mul_sum, ← Complex.re_sum]
  congr 2
  push_cast
  simp only [Arith.bar_eq, Finset.mul_sum, map_sum, map_mul, IsCMField.complexEmbedding_complexConj]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

private theorem e1 {E : Type} [Field E] [NumberField E] {n : ℕ} (q : ℚ) (a : Fin n → 𝓞 E) :
    (1 : ℝ) ⊗ₜ[ℚ] (q ⊗ₜ[ℤ] a) = (q : ℝ) • ((1 : ℝ) ⊗ₜ[ℚ] ((1 : ℚ) ⊗ₜ[ℤ] a)) := by
  rw [show (q ⊗ₜ[ℤ] a : ℚ ⊗[ℤ] (Fin n → 𝓞 E)) = q • ((1 : ℚ) ⊗ₜ[ℤ] a) by
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one],
    ← TensorProduct.smul_tmul, TensorProduct.smul_tmul', smul_eq_mul, mul_one, Rat.smul_one_eq_cast]

private theorem core1 (hT : TraceType) {E : Type} [Field E] [NumberField E] [IsCMField E] (A : Arith E) (n : ℕ)
    (β : ℚ ⊗[ℤ] (Fin n → 𝓞 E) →ₗ[ℚ] (Fin n → E)) (hβ : ∀ (v : Fin n → 𝓞 E) i, β (1 ⊗ₜ v) i = (v i : E))
    (w w' : ℚ ⊗[ℤ] (Fin n → 𝓞 E)) :
    (((A.EF n).baseChange ℚ w w' : ℚ) : ℝ) =
      R (fun k : Phi A × Fin n => k.1.1 A.δ * k.1.1 (A.hd n k.2 : E))
        (Th (fun τ : Phi A => τ.1) β ((1 : ℝ) ⊗ₜ w)) (Th (fun τ : Phi A => τ.1) β ((1 : ℝ) ⊗ₜ w')) := by
  induction w using TensorProduct.induction_on with
  | zero => simp [R]
  | add a b ha hb =>
    rw [TensorProduct.tmul_add, map_add, map_add, LinearMap.add_apply, Rat.cast_add, ha, hb, R_add_l]
  | tmul q a =>
    induction w' using TensorProduct.induction_on with
    | zero => simp [R]
    | add a b ha hb =>
      rw [TensorProduct.tmul_add, map_add, map_add, Rat.cast_add, ha, hb, R_add_r]
    | tmul t b =>
      rw [LinearMap.BilinForm.baseChange_tmul, e1 q a, e1 t b, map_smul, map_smul, R_smul_l, R_smul_r]
      have h : R (fun k : Phi A × Fin n => k.1.1 A.δ * k.1.1 (A.hd n k.2 : E))
          (Th (fun τ : Phi A => τ.1) β ((1 : ℝ) ⊗ₜ ((1 : ℚ) ⊗ₜ a)))
          (Th (fun τ : Phi A => τ.1) β ((1 : ℝ) ⊗ₜ ((1 : ℚ) ⊗ₜ b))) = ((A.EF n a b : ℤ) : ℝ) := by
        rw [core0 hT A n a b]
        refine Finset.sum_congr rfl fun k _ => ?_
        simp only [Th_tmul, one_smul, hβ]
      rw [h]
      simp [Rat.smul_def, zsmul_eq_mul]
      ring

theorem UpperTheory.cmField_hermitianForm_baseChange_real_eq_sum :
    TraceType → ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] (A : Arith E) (n : ℕ) (β : ℚ ⊗[ℤ] (Fin n → 𝓞 E) →ₗ[ℚ] (Fin n → E)), (∀ (v : Fin n → 𝓞 E) i, β (1 ⊗ₜ v) i = (v i : E)) → ∀ x y : ℝ ⊗[ℚ] (ℚ ⊗[ℤ] (Fin n → 𝓞 E)), ((A.EF n).baseChange ℚ).baseChange ℝ x y = ∑ k : Phi A × Fin n, 2 * (k.1.1 A.δ * k.1.1 (A.hd n k.2 : E) * Th (fun τ : Phi A => τ.1) β x k * (starRingEnd ℂ) (Th (fun τ : Phi A => τ.1) β y k)).re := by
  intro hT E _ _ _ A n β hβ x y
  change _ = R (fun k : Phi A × Fin n => k.1.1 A.δ * k.1.1 (A.hd n k.2 : E))
    (Th (fun τ : Phi A => τ.1) β x) (Th (fun τ : Phi A => τ.1) β y)
  induction x using TensorProduct.induction_on with
  | zero => simp [R]
  | add a b ha hb => rw [map_add, map_add, LinearMap.add_apply, ha, hb, R_add_l]
  | tmul r w =>
    induction y using TensorProduct.induction_on with
    | zero => simp [R]
    | add a b ha hb => rw [map_add, map_add, ha, hb, R_add_r]
    | tmul s w' =>
      have e : ∀ (r : ℝ) (w : ℚ ⊗[ℤ] (Fin n → 𝓞 E)), r ⊗ₜ[ℚ] w = r • ((1 : ℝ) ⊗ₜ[ℚ] w) := by
        intro r w
        rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      rw [LinearMap.BilinForm.baseChange_tmul, e r w, e s w', map_smul, map_smul, R_smul_l, R_smul_r, ← core1 hT A n β hβ w w',
        Rat.smul_def]
      simp only [mul_comm, mul_left_comm, mul_assoc]
