import Formalism.GaussJetBounds.GenLogInverse
import Formalism.GaussJetBounds.StatementN
import Formalism.GaussJetBounds.MonoShapeTop
import Formalism.GaussJetBounds.GaussJetProofs.NormDetLeOneOfEntries
import Formalism.GaussJetBounds.GaussJetProofs.ThmAOp

noncomputable section
open scoped BigOperators

universe u

namespace Formalism.DworkPowerSeriesWeights

open MvPolynomial

lemma minorProd_map {R : Type u} [CommRing R] {σ τ : Type} {N0 N1 Cn : ℕ}
    (φ : MvPolynomial σ R →ₐ[R] MvPolynomial τ R)
    (row : Fin N0 → Fin N1 → MvPolynomial σ R) (p : Fin Cn → ℕ) (hp : ∀ c, p c ≤ N0)
    (I : ∀ c, Fin (p c) → Fin N1) :
    φ (minorProd row p hp I) = minorProd (fun i b => φ (row i b)) p hp I := by
  unfold minorProd
  rw [map_prod]
  refine Finset.prod_congr rfl fun c _ => ?_
  rw [AlgHom.map_det]
  rfl

theorem one_row_bound : OneRow.{u} := by
  intro K _ _ N0 N1 Cn f hf hdet x hx p hp I
  classical
  have hne : f.det ≠ 0 := by
    intro h
    rw [h, norm_zero] at hdet
    exact zero_ne_one hdet
  have hunit : IsUnit f.det := isUnit_iff_ne_zero.mpr hne
  let X0 : Matrix (Fin N0) (Fin N0) K := Matrix.of x
  let γ : Matrix (Fin N0) (Fin N0) K := X0 * f⁻¹
  have hγint : ∀ i k, ‖γ i k‖ ≤ 1 := by
    intro i k
    show ‖(X0 * f⁻¹) i k‖ ≤ 1
    rw [Matrix.mul_apply]
    refine IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun a _ => ?_
    rw [norm_mul]
    exact mul_le_one₀ (hx i a) (norm_nonneg _) (norm_inv_entry_le_one f hf hdet a k)
  have hγf : ∀ i a, (∑ k, γ i k * f k a) = x i a := by
    intro i a
    rw [← Matrix.mul_apply]
    show (X0 * f⁻¹ * f) i a = x i a
    rw [Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hunit, Matrix.mul_one]
    rfl
  refine ⟨minorProd (oldRowLow (N1 := N1) (fun i k => γ i k)) p hp I, ?_, ?_, ?_⟩
  · refine minorProd_mem_opInt _ (fun i b => ?_) p hp I
    unfold oldRowLow
    refine Subring.sum_mem _ fun k _ => ?_
    intro κ
    rw [coeff_C_mul, coeff_X, norm_mul]
    refine mul_le_one₀ (hγint i k) (norm_nonneg _) ?_
    split_ifs <;> simp
  · rw [minorProd_map]
    congr 1
    funext i b
    unfold oldRowLow
    simp only [map_sum, map_mul, aeval_X, algHom_C, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [← hγf i a, map_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_mul, mul_assoc]
    rfl
  · intro mono hm a
    exact (monoShapeLow K N0 N1 N0 Cn (fun i k => γ i k) p hp I mono hm).2 a

theorem base_size_bounds : SizesB := by
  intro H _ _ TT c wt wt' f k b b' hcard hk hb hb' hc1 hc2 hwt hwt'
  constructor
  · have h1 : ∀ t, c t ≤ 4 * k * b' + (if t ∈ TT then 2 * b else 0) := by
      intro t
      split_ifs with h
      · exact hc2 t h
      · rw [add_zero]; exact hc1 t h
    calc (∑ t, c t) ≤ ∑ t, (4 * k * b' + (if t ∈ TT then 2 * b else 0)) :=
          Finset.sum_le_sum fun t _ => h1 t
      _ = 2 * (TT.card : ℝ) * b + 2 * f * k * b' := by
          rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hcard,
            Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, nsmul_eq_mul]
          ring
  · have hf : 0 ≤ f := by
      have : (0 : ℝ) ≤ (Fintype.card H : ℝ) := Nat.cast_nonneg _
      linarith
    have h0 : 0 ≤ ∑ t, min (wt t) (wt' t) :=
      Finset.sum_nonneg fun t _ => le_min (hwt t).1 (hwt' t)
    have h1 : (∑ t, min (wt t) (wt' t)) ≤ f * b' := by
      calc (∑ t, min (wt t) (wt' t)) ≤ ∑ _t : H, 2 * b' :=
            Finset.sum_le_sum fun t _ => (min_le_left _ _).trans (hwt t).2
        _ = f * b' := by
            rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hcard]
            ring
    rw [abs_mul, abs_neg, abs_of_nonneg (by linarith : 0 ≤ (k - 1) / 2), abs_of_nonneg h0]
    have hfb : 0 ≤ f * b' := mul_nonneg hf hb'
    calc (k - 1) / 2 * ∑ t, min (wt t) (wt' t) ≤ (k - 1) / 2 * (f * b') :=
          mul_le_mul_of_nonneg_left h1 (by linarith)
      _ ≤ k * (f * b') := mul_le_mul_of_nonneg_right (by linarith) hfb
      _ = f * k * b' := by ring

end Formalism.DworkPowerSeriesWeights
