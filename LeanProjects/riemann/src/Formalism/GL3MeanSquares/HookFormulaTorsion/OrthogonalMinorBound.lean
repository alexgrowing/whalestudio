import Mathlib
import Formalism.GL3MeanSquares.ConcavityEquidistribution
import Formalism.LogVandermondeBounds.LogVandermondeProofs.GammaIntegralPolynomialBound

namespace Formalism.HermitianLattices.TraceIntegrality

open Finset Matrix
open scoped ComplexOrder

theorem am_gm_sum_lower_bound : AmGmSumLowerBound := by
  intro f v x hf hv hx hprod
  have h := Formalism.LogVandermondeBounds.flipTwoThree.amgm_period_lattice_bound f (2 * v ^ 2) x hf (by positivity) hx
    (by
      have e : (2 * (2 * v ^ 2)) ^ f = (2 * v) ^ (2 * f) := by
        rw [pow_mul]; congr 1; ring
      rw [e]; exact hprod)
  have e : (f : ℝ) / (2 * v) ^ 2 = ((f : ℝ) / (2 * v ^ 2)) / 2 := by
    field_simp
  rw [e]
  linarith

theorem concavity_equidistribution : ConcavityEquidistribution := by
  intro ι σ _ _ _ _ π c y B hfib hy hB
  classical
  have hcardσ : (Fintype.card σ : ℝ) = c * Fintype.card ι := by
    have h := Finset.card_eq_sum_card_fiberwise (f := π) (s := (univ : Finset σ))
      (t := (univ : Finset ι)) (fun _ _ => Finset.mem_coe.2 (mem_univ _))
    simp only [hfib, sum_const, smul_eq_mul, card_univ] at h
    rw [h]; push_cast; ring
  have hσpos : (0 : ℝ) < Fintype.card σ := by exact_mod_cast Fintype.card_pos
  have hc : (0 : ℝ) < c := by
    rcases Nat.eq_zero_or_pos c with h | h
    · rw [h] at hcardσ; simp at hcardσ
    · exact_mod_cast h
  have hι : (0 : ℝ) < Fintype.card ι := by
    have : (0 : ℝ) < c * Fintype.card ι := hcardσ ▸ hσpos
    exact (pos_iff_pos_of_mul_pos this).1 hc
  have hsum : ∑ s, Real.log (y (π s)) = c * ∑ τ, Real.log (y τ) := by
    have h := Finset.sum_fiberwise (s := (univ : Finset σ)) (g := π)
      (f := fun s => Real.log (y (π s)))
    rw [← h, Finset.mul_sum]
    refine Finset.sum_congr rfl fun τ _ => ?_
    rw [Finset.sum_congr rfl (g := fun _ => Real.log (y τ))
      (fun s hs => by rw [(mem_filter.1 hs).2])]
    rw [sum_const, hfib, nsmul_eq_mul]
  have hw : ∑ _τ : ι, (Fintype.card ι : ℝ)⁻¹ = 1 := by
    rw [sum_const, card_univ, nsmul_eq_mul]; field_simp
  have hj := strictConcaveOn_log_Ioi.concaveOn.le_map_sum (t := (univ : Finset ι))
    (w := fun _ => (Fintype.card ι : ℝ)⁻¹) (p := y) (fun _ _ => by positivity) hw
    (fun τ _ => hy τ)
  simp only [smul_eq_mul, ← Finset.mul_sum] at hj
  have hSpos : 0 < ∑ τ, y τ := by
    have : Nonempty ι := ⟨π (Classical.arbitrary σ)⟩
    exact Finset.sum_pos (fun τ _ => hy τ) univ_nonempty
  unfold mean
  rw [hsum, hcardσ]
  calc (c * ∑ τ, Real.log (y τ)) / (c * Fintype.card ι)
      = (Fintype.card ι : ℝ)⁻¹ * ∑ τ, Real.log (y τ) := by field_simp
    _ ≤ Real.log ((Fintype.card ι : ℝ)⁻¹ * ∑ τ, y τ) := hj
    _ ≤ Real.log (B / Fintype.card ι) := by
        apply Real.log_le_log (by positivity)
        rw [div_eq_inv_mul]
        exact mul_le_mul_of_nonneg_left hB (by positivity)

private lemma one_le_det_one_add {r : ℕ} (R : Matrix (Fin r) (Fin r) ℂ) (hR : R.PosSemidef) :
    1 ≤ (1 + R).det.re := by
  have hH := hR.isHermitian
  have e : (1 + R).det = ((∏ i, (1 + hH.eigenvalues i) : ℝ) : ℂ) := by
    have h1 : 1 + R = Unitary.conjStarAlgAut ℂ _ hH.eigenvectorUnitary
        (1 + diagonal (RCLike.ofReal ∘ hH.eigenvalues)) := by
      rw [map_add, map_one, ← hH.spectral_theorem]
    rw [h1, Unitary.conjStarAlgAut_apply, det_mul_comm, ← mul_assoc]
    have h2 : (1 : Matrix (Fin r) (Fin r) ℂ) + diagonal (RCLike.ofReal ∘ hH.eigenvalues)
        = diagonal (fun i => (1 : ℂ) + (hH.eigenvalues i : ℂ)) := by
      rw [← diagonal_one, diagonal_add]; rfl
    rw [h2]
    simp [det_diagonal]
  rw [e, Complex.ofReal_re]
  have : ∀ i ∈ (univ : Finset (Fin r)), (1 : ℝ) ≤ 1 + hH.eigenvalues i := fun i _ => by
    have := hR.eigenvalues_nonneg i
    linarith
  calc (1 : ℝ) = ∏ _i : Fin r, (1 : ℝ) := by simp
    _ ≤ _ := Finset.prod_le_prod (fun _ _ => zero_le_one) this

private lemma minor_le_gram {r n : ℕ} (A : Matrix (Fin r) (Fin n) ℂ) (e : Fin r → Fin n)
    (he : Function.Injective e) :
    ‖(A.submatrix id e).det‖ ^ 2 ≤ (A * A.conjTranspose).det.re := by
  classical
  set B := A.submatrix id e with hB
  have hpsd : (A * A.conjTranspose).PosSemidef := posSemidef_self_mul_conjTranspose A
  by_cases hdet : B.det = 0
  · rw [hdet]
    have := (Complex.le_def.1 hpsd.det_nonneg).1
    simpa using this
  set Q : Matrix (Fin r) (Fin r) ℂ :=
    A * diagonal (fun j => if j ∈ Set.range e then (0 : ℂ) else 1) * A.conjTranspose with hQ
  have hQpsd : Q.PosSemidef := by
    apply PosSemidef.mul_mul_conjTranspose_same
    apply PosSemidef.diagonal
    intro j
    dsimp only
    split_ifs <;> simp
  have hsplit : A * A.conjTranspose = B * B.conjTranspose + Q := by
    ext i k
    rw [hQ, hB, Matrix.add_apply, mul_apply, mul_apply, mul_apply]
    simp only [mul_diagonal, conjTranspose_apply, submatrix_apply, id]
    have h1 : ∑ l, A i (e l) * star (A k (e l))
        = ∑ j, if j ∈ Set.range e then A i j * star (A k j) else 0 := by
      rw [← Finset.sum_filter]
      have : (univ.filter fun j => j ∈ Set.range e) = univ.image e := by
        ext j; simp [eq_comm]
      rw [this, Finset.sum_image (fun a _ b _ h => he h)]
    rw [h1, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    split_ifs <;> simp
  have hu : IsUnit B.det := isUnit_iff_ne_zero.2 hdet
  set R : Matrix (Fin r) (Fin r) ℂ := B⁻¹ * Q * (B⁻¹).conjTranspose with hR
  have hRpsd : R.PosSemidef := hQpsd.mul_mul_conjTranspose_same _
  have hfac : A * A.conjTranspose = B * (1 + R) * B.conjTranspose := by
    rw [hsplit, hR, mul_add, add_mul, mul_one]
    congr 1
    have h1 : B * B⁻¹ = 1 := mul_nonsing_inv B hu
    have h2 : (B⁻¹).conjTranspose * B.conjTranspose = 1 := by
      rw [← conjTranspose_mul, h1, conjTranspose_one]
    calc Q = (B * B⁻¹) * Q * ((B⁻¹).conjTranspose * B.conjTranspose) := by
          rw [h1, h2, one_mul, mul_one]
      _ = _ := by simp only [Matrix.mul_assoc]
  rw [hfac, det_mul, det_mul, det_conjTranspose]
  have h3 := one_le_det_one_add R hRpsd
  have him : (1 + R).det.im = 0 := by
    have := (PosSemidef.one.add hRpsd).det_nonneg
    exact (Complex.le_def.1 this).2.symm
  have h4 : (B.det * (1 + R).det * star B.det).re = ‖B.det‖ ^ 2 * (1 + R).det.re := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
    simp only [Complex.mul_re, Complex.mul_im, Complex.star_def, Complex.conj_re, Complex.conj_im,
      him]
    ring
  rw [h4]
  nlinarith [sq_nonneg ‖B.det‖]

theorem orthogonal_minor_bound : OrthogonalMinorBound := by
  intro r n A d e hd he
  classical
  set S : Matrix (Fin n) (Fin n) ℂ := diagonal (fun i => ((Real.sqrt (d i) : ℝ) : ℂ)) with hS
  have hSS : S * S.conjTranspose = diagonal (fun i => (d i : ℂ)) := by
    rw [hS, diagonal_conjTranspose, diagonal_mul_diagonal]
    congr 1
    ext i
    simp only [Pi.star_apply, Complex.star_def, Complex.conj_ofReal]
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (hd i).le]
  have hgram : A * diagonal (fun i => (d i : ℂ)) * A.conjTranspose
      = (A * S) * (A * S).conjTranspose := by
    rw [conjTranspose_mul, ← hSS]
    simp only [Matrix.mul_assoc]
  have hsub : (A * S).submatrix id e
      = A.submatrix id e * diagonal (fun i => ((Real.sqrt (d (e i)) : ℝ) : ℂ)) := by
    ext i k
    simp [hS, mul_apply, diagonal_apply]
  have h := minor_le_gram (A * S) e he
  rw [hgram]
  refine le_trans (le_of_eq ?_) h
  rw [hsub, det_mul, det_diagonal, norm_mul, mul_pow]
  congr 1
  rw [norm_prod, ← Finset.prod_pow]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [Complex.norm_real, Real.norm_eq_abs, sq_abs, Real.sq_sqrt (hd _).le]

end Formalism.HermitianLattices.TraceIntegrality
