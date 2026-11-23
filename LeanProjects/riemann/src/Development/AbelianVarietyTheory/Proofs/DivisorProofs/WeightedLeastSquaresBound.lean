import Mathlib
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.CasimirCoefficients.CBinet

open scoped ComplexOrder Matrix

namespace GlobalTheory.WeightedLS

open Matrix

variable {M g : ℕ}

theorem det_pos (L : Matrix (Fin M) (Fin g) ℝ) (hL : L.rank = g) (D : Fin M → ℝ)
    (hD : ∀ k, 0 < D k) : 0 < (L.transpose * Matrix.diagonal D * L).det := by
  have hinj : Function.Injective L.mulVec := by
    have h := LinearMap.finrank_range_add_finrank_ker L.mulVecLin
    have h2 : Module.finrank ℝ (LinearMap.range L.mulVecLin) = g := hL
    rw [h2, Module.finrank_fin_fun] at h
    have h3 : Module.finrank ℝ (LinearMap.ker L.mulVecLin) = 0 := by omega
    have h4 : LinearMap.ker L.mulVecLin = ⊥ := Submodule.finrank_eq_zero.mp h3
    exact LinearMap.ker_eq_bot.mp h4
  have hP : (Matrix.diagonal D).PosDef := Matrix.posDef_diagonal_iff.mpr hD
  have h := hP.conjTranspose_mul_mul_same hinj
  rw [Matrix.conjTranspose_eq_transpose_of_trivial] at h
  exact h.det_pos

theorem det_eq_sum (L X : Matrix (Fin M) (Fin g) ℝ) (D : Fin M → ℝ) :
    (L.transpose * Matrix.diagonal D * X).det = ∑ S : {S : Finset (Fin M) // S.card = g},
      (∏ j, D (S.1.orderEmbOfFin S.2 j)) * ((L.submatrix (S.1.orderEmbOfFin S.2) id).det *
        (X.submatrix (S.1.orderEmbOfFin S.2) id).det) := by
  rw [ReciprocityTheory.ChartRestriction.DS.S7.det_mul_eq_sum_submatrix]
  refine Finset.sum_congr rfl fun S _ => ?_
  have h : (L.transpose * Matrix.diagonal D).submatrix id (S.1.orderEmbOfFin S.2) =
      (L.submatrix (S.1.orderEmbOfFin S.2) id).transpose *
        Matrix.diagonal (fun j => D (S.1.orderEmbOfFin S.2 j)) := by
    ext i j
    simp [Matrix.mul_diagonal]
  rw [h, Matrix.det_mul, Matrix.det_transpose, Matrix.det_diagonal]
  ring

theorem block_bound (A : Matrix (Fin g) (Fin g) ℝ) : ∃ K : ℝ, 0 ≤ K ∧
    ∀ (c : Fin g → ℝ) (k : Fin g),
      |A.det * (A.updateCol k c).det| ≤ K * ‖c‖ * (A.det * A.det) := by
  by_cases hA : A.det = 0
  · exact ⟨0, le_rfl, fun c k => by simp [hA]⟩
  · let f : (Fin g → ℝ) →L[ℝ] (Fin g → ℝ) := LinearMap.toContinuousLinearMap (Matrix.cramer A)
    have hp : 0 < |A.det| := abs_pos.mpr hA
    refine ⟨‖f‖ / |A.det|, by positivity, fun c k => ?_⟩
    have h1 : |(A.updateCol k c).det| ≤ ‖f‖ * ‖c‖ := by
      have h2 : (A.updateCol k c).det = f c k := by
        simp [f, Matrix.cramer_apply]
      rw [h2]
      exact (norm_le_pi_norm (f c) k).trans (f.le_opNorm c)
    rw [abs_mul, ← abs_mul_abs_self A.det]
    calc |A.det| * |(A.updateCol k c).det| ≤ |A.det| * (‖f‖ * ‖c‖) :=
          mul_le_mul_of_nonneg_left h1 hp.le
      _ = _ := by field_simp

theorem weighted_least_squares_bound : ∀ (M g : ℕ) (L : Matrix (Fin M) (Fin g) ℝ), L.rank = g →
    ∃ K : ℝ, ∀ (D : Fin M → ℝ) (b : Fin M → ℝ), (∀ k, 0 < D k) →
      ‖((L.transpose * Matrix.diagonal D * L)⁻¹ * L.transpose * Matrix.diagonal D).mulVec b‖ ≤
        K * ‖b‖ := by
  intro M g L hL
  choose K hK0 hK using fun S : {S : Finset (Fin M) // S.card = g} =>
    block_bound (L.submatrix (S.1.orderEmbOfFin S.2) id)
  refine ⟨∑ S, K S, fun D b hD => ?_⟩
  have hKs : 0 ≤ ∑ S, K S := Finset.sum_nonneg fun S _ => hK0 S
  have hdet := det_pos L hL D hD
  set A := L.transpose * Matrix.diagonal D * L with hA
  refine (pi_norm_le_iff_of_nonneg (by positivity)).mpr fun k => ?_
  have hx : A.det * (A⁻¹ * L.transpose * Matrix.diagonal D).mulVec b k =
      (L.transpose * Matrix.diagonal D * L.updateCol k b).det := by
    have h1 := Matrix.det_smul_inv_mulVec_eq_cramer A ((L.transpose * Matrix.diagonal D).mulVec b)
      (isUnit_iff_ne_zero.mpr hdet.ne')
    have h2 := congrFun h1 k
    rw [Matrix.cramer_apply, Matrix.mulVec_mulVec, ← Matrix.mul_assoc] at h2
    rw [← smul_eq_mul, ← Pi.smul_apply, h2]
    congr 1
    ext i j
    by_cases hj : j = k
    · subst hj
      simp [Matrix.mul_apply (M := L.transpose * Matrix.diagonal D), Matrix.mulVec, dotProduct]
    · simp [hA, Matrix.mul_apply (M := L.transpose * Matrix.diagonal D), Matrix.updateCol_ne hj]
  have hb : |(L.transpose * Matrix.diagonal D * L.updateCol k b).det| ≤
      (∑ S, K S) * ‖b‖ * A.det := by
    rw [hA, det_eq_sum, det_eq_sum, Finset.mul_sum]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun S _ => ?_)
    set e := S.1.orderEmbOfFin S.2 with he
    have hp : 0 ≤ ∏ j, D (e j) := Finset.prod_nonneg fun j _ => (hD _).le
    have hu : (L.updateCol k b).submatrix e id = (L.submatrix e id).updateCol k (b ∘ e) := by
      ext i j
      by_cases hj : j = k
      · subst hj; simp
      · simp [Matrix.updateCol_ne hj]
    have hn : ‖b ∘ e‖ ≤ ‖b‖ :=
      (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr fun i => norm_le_pi_norm b (e i)
    have hKS : K S ≤ ∑ S, K S :=
      Finset.single_le_sum (f := K) (fun S _ => hK0 S) (Finset.mem_univ S)
    rw [abs_mul, abs_of_nonneg hp, hu, mul_left_comm]
    refine mul_le_mul_of_nonneg_left ((hK S (b ∘ e) k).trans ?_) hp
    exact mul_le_mul_of_nonneg_right (mul_le_mul hKS hn (norm_nonneg _) hKs) (mul_self_nonneg _)
  rw [← hx, abs_mul, abs_of_pos hdet, mul_comm] at hb
  exact le_of_mul_le_mul_right hb hdet

end GlobalTheory.WeightedLS
