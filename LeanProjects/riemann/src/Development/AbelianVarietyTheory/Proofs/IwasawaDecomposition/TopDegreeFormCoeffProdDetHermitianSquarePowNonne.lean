import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsNegSqZero
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TopDegreeFormCoeffLinearSubstEqAbsDetSqMul

set_option autoImplicit false

noncomputable section

open Matrix MvPolynomial GlobalTheory.GoodMetric GlobalTheory.HermFrame GlobalTheory.PointFormSign
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ComplexOrder Topology

namespace GlobalTheory.PointFormSign.TopPos

open GlobalTheory.GoodMetric.LinSubst

variable {n : ℕ}

def pairForm (u v : Fin n → ℂ) : MvPolynomial (Fin n × Fin n) ℂ :=
  ∑ p : Fin n × Fin n, C (u p.1 * starRingEnd ℂ (v p.2)) * X p

theorem topCoeff_prod_pairForm_fin (k : ℕ) :
    ∃ D : (Fin k → Fin n → ℂ) → ℂ, ∀ u v : Fin k → Fin n → ℂ,
      topCoeff (∏ j, pairForm (u j) (v j)) = D u * starRingEnd ℂ (D v) := by
  by_cases hk : k = n
  · subst hk
    refine ⟨fun u => (Matrix.of u).det, fun u v => ?_⟩
    simp only [pairForm]
    rw [Finset.prod_univ_sum, Fintype.piFinset_univ, topCoeff_sum]
    simp_rw [Finset.prod_mul_distrib, ← map_prod, topCoeff_C_mul]
    rw [← (Equiv.arrowProdEquivProdArrow (Fin k) (fun _ => Fin k) (fun _ => Fin k)).symm.sum_comp,
      Fintype.sum_prod_type]
    simp only [Equiv.arrowProdEquivProdArrow, Equiv.coe_fn_symm_mk]
    simp_rw [topCoeff_prod_X_pair]
    have key : ∀ (c d : Fin k → Fin k),
        (∏ i, u i (c i) * starRingEnd ℂ (v i (d i))) * ((rowSel c).det * (rowSel d).det) =
        ((∏ i, (Matrix.of u) i (c i)) * (rowSel c).det) *
        ((∏ i, ((Matrix.of v).map (starRingEnd ℂ)) i (d i)) * (rowSel d).det) := by
      intro c d
      simp only [Matrix.of_apply, Matrix.map_apply, Finset.prod_mul_distrib]
      ring
    rw [Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => key c d, ← Finset.sum_mul_sum,
      sum_prod_mul_det_rowSel, sum_prod_mul_det_rowSel, RingHom.map_det]
    rfl
  · refine ⟨fun _ => 0, fun u v => ?_⟩
    simp only [pairForm]
    rw [Finset.prod_univ_sum, Fintype.piFinset_univ, topCoeff_sum]
    simp_rw [Finset.prod_mul_distrib, ← map_prod, topCoeff_C_mul]
    simp [topCoeff_prod_X_of_ne hk]

theorem topCoeff_prod_pairForm (J : Type) [Fintype J] :
    ∃ D : (J → Fin n → ℂ) → ℂ, ∀ u v : J → Fin n → ℂ,
      topCoeff (∏ j, pairForm (u j) (v j)) = D u * starRingEnd ℂ (D v) := by
  obtain ⟨D, hD⟩ := topCoeff_prod_pairForm_fin (n := n) (Fintype.card J)
  let e := (Fintype.equivFin J).symm
  refine ⟨fun u => D (u ∘ e), fun u v => ?_⟩
  rw [← hD, ← e.prod_comp]
  rfl

theorem factorial_mul_det {R : Type} [CommRing R] {m : ℕ} (M : Matrix (Fin m) (Fin m) R) :
    (m.factorial : R) * M.det = ∑ σ : Equiv.Perm (Fin m), ∑ τ : Equiv.Perm (Fin m),
      ((Equiv.Perm.sign σ : ℤ) : R) * ((Equiv.Perm.sign τ : ℤ) : R) * ∏ i, M (σ i) (τ i) := by
  rw [Finset.sum_comm]
  have h (τ : Equiv.Perm (Fin m)) : ∑ σ : Equiv.Perm (Fin m),
      ((Equiv.Perm.sign σ : ℤ) : R) * ((Equiv.Perm.sign τ : ℤ) : R) * ∏ i, M (σ i) (τ i) = M.det := by
    have h1 := Matrix.det_permute' τ M
    rw [Matrix.det_apply'] at h1
    have h2 : ((Equiv.Perm.sign τ : ℤ) : R) * ((Equiv.Perm.sign τ : ℤ) : R) = 1 := by
      rw [← Int.cast_mul, ← Units.val_mul, Int.units_mul_self]
      simp
    calc _ = ((Equiv.Perm.sign τ : ℤ) : R) * ∑ σ : Equiv.Perm (Fin m),
          ((Equiv.Perm.sign σ : ℤ) : R) * ∏ i, (M.submatrix id τ) (σ i) i := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun σ _ => ?_
          simp only [Matrix.submatrix_apply, id]
          ring
      _ = M.det := by rw [h1, ← mul_assoc, h2, one_mul]
  simp_rw [h]
  simp [Fintype.card_perm]

theorem sqPoly_apply {m r : ℕ} (T : V n →ₗ[ℂ] Matrix (Fin m) (Fin r) ℂ) (i j : Fin m) :
    sqPoly T i j = ∑ k, pairForm (fun a => T (coordVec a) i k) (fun a => T (coordVec a) j k) := by
  simp only [sqPoly, pairForm, Matrix.of_apply, Matrix.mul_apply, Matrix.conjTranspose_apply, map_sum,
    Finset.sum_mul, Fintype.sum_prod_type]
  rw [Finset.sum_comm (γ := Fin r)]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_comm (γ := Fin r)]
  rfl

theorem factorial_mul_det_sqPoly {m r : ℕ} (T : V n →ₗ[ℂ] Matrix (Fin m) (Fin r) ℂ) :
    C (m.factorial : ℂ) * (sqPoly T).det = ∑ k : Fin m → Fin r, ∑ σ : Equiv.Perm (Fin m), ∑ τ : Equiv.Perm (Fin m),
      C (((Equiv.Perm.sign σ : ℤ) : ℂ) * ((Equiv.Perm.sign τ : ℤ) : ℂ)) *
        ∏ i, pairForm (fun a => T (coordVec a) (σ i) (k i)) (fun a => T (coordVec a) (τ i) (k i)) := by
  rw [map_natCast, factorial_mul_det]
  simp_rw [sqPoly_apply, Finset.prod_univ_sum, Fintype.piFinset_univ, Finset.mul_sum]
  rw [Finset.sum_comm (γ := Fin m → Fin r)]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [Finset.sum_comm (γ := Fin m → Fin r)]
  simp only [map_mul, map_intCast]

theorem topCoeff_prod_det_nonneg {B : Type} [Fintype B] (m r : B → ℕ)
    (T : ∀ b, V n →ₗ[ℂ] Matrix (Fin (m b)) (Fin (r b)) ℂ) :
    0 ≤ topCoeff (∏ b, (sqPoly (T b)).det) := by
  classical
  obtain ⟨D, hD⟩ := topCoeff_prod_pairForm (n := n) (Σ b, Fin (m b))
  have h : (∏ b, ((m b).factorial : ℂ)) * topCoeff (∏ b, (sqPoly (T b)).det) =
      ∑ k : ∀ b, Fin (m b) → Fin (r b),
        (∑ σ : ∀ b, Equiv.Perm (Fin (m b)), (∏ b, ((Equiv.Perm.sign (σ b) : ℤ) : ℂ)) *
          D fun j a => T j.1 (coordVec a) (σ j.1 j.2) (k j.1 j.2)) *
        starRingEnd ℂ (∑ σ : ∀ b, Equiv.Perm (Fin (m b)), (∏ b, ((Equiv.Perm.sign (σ b) : ℤ) : ℂ)) *
          D fun j a => T j.1 (coordVec a) (σ j.1 j.2) (k j.1 j.2)) := by
    rw [← topCoeff_C_mul, map_prod, ← Finset.prod_mul_distrib]
    simp_rw [factorial_mul_det_sqPoly]
    rw [Finset.prod_univ_sum, Fintype.piFinset_univ, topCoeff_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Finset.prod_univ_sum, Fintype.piFinset_univ, topCoeff_sum, map_sum, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [Finset.prod_univ_sum, Fintype.piFinset_univ, topCoeff_sum]
    refine Finset.sum_congr rfl fun τ _ => ?_
    rw [Finset.prod_mul_distrib, ← map_prod, topCoeff_C_mul, ← Fintype.prod_sigma', hD, Finset.prod_mul_distrib]
    simp only [map_mul, map_prod, map_intCast]
    ring
  have h0 : 0 ≤ (∏ b, ((m b).factorial : ℂ)) * topCoeff (∏ b, (sqPoly (T b)).det) := by
    rw [h]
    exact Finset.sum_nonneg fun k _ => mul_star_self_nonneg _
  have hN : (0 : ℝ) < ∏ b, ((m b).factorial : ℝ) :=
    Finset.prod_pos fun b _ => by exact_mod_cast Nat.factorial_pos _
  have e : (∏ b, ((m b).factorial : ℂ)) = ((∏ b, ((m b).factorial : ℝ) : ℝ) : ℂ) := by push_cast; rfl
  rw [e] at h0
  have h1 : (0 : ℂ) ≤ (((∏ b, ((m b).factorial : ℝ))⁻¹ : ℝ) : ℂ) := Complex.zero_le_real.2 (inv_nonneg.2 hN.le)
  have h2 := mul_nonneg h1 h0
  rwa [← mul_assoc, ← Complex.ofReal_mul, inv_mul_cancel₀ hN.ne', Complex.ofReal_one, one_mul] at h2

end GlobalTheory.PointFormSign.TopPos

theorem GlobalTheory.PointFormSign.topCoeff_prod_det_sqPoly_pow_nonneg {n : ℕ} {κ : Type} [Fintype κ] (m r e : κ → ℕ)
    (T : ∀ t, V n →ₗ[ℂ] Matrix (Fin (m t)) (Fin (r t)) ℂ) :
    0 ≤ topCoeff (∏ t, (sqPoly (T t)).det ^ e t) := by
  have h := TopPos.topCoeff_prod_det_nonneg (B := Σ t, Fin (e t)) (fun b => m b.1) (fun b => r b.1) fun b => T b.1
  rw [Fintype.prod_sigma] at h
  refine h.trans_eq (congrArg topCoeff (Finset.prod_congr rfl fun t _ => ?_))
  exact (Finset.prod_const (s := Finset.univ) (sqPoly (T t)).det).trans (by rw [Finset.card_univ, Fintype.card_fin])
