import Mathlib
open MeasureTheory
open scoped ComplexOrder

namespace GlobalTheory

open Matrix
open scoped MatrixOrder

private lemma ellvol_factor {g : ℕ} {G : Matrix (Fin g) (Fin g) ℂ} (hG : G.PosDef) :
    ∃ B : Matrix (Fin g) (Fin g) ℂ, G = Bᴴ * B := by
  have h0 : 0 ≤ G := hG.posSemidef.nonneg
  refine ⟨CFC.sqrt G, ?_⟩
  have hs : IsSelfAdjoint (CFC.sqrt G) := (CFC.sqrt_nonneg G).isSelfAdjoint
  rw [show (CFC.sqrt G)ᴴ = CFC.sqrt G from hs.star_eq, CFC.sqrt_mul_sqrt_self G h0]

private lemma ellvol_form {g : ℕ} (Hm B : Matrix (Fin g) (Fin g) ℂ) (hB : Hmᵀ = Bᴴ * B)
    (w : Fin g → ℂ) : (w ⬝ᵥ Hm *ᵥ star w).re = ∑ k, ‖(B *ᵥ w) k‖ ^ 2 := by
  have h1 : w ⬝ᵥ Hm *ᵥ star w = star (B *ᵥ w) ⬝ᵥ (B *ᵥ w) := by
    rw [dotProduct_mulVec, ← mulVec_transpose, dotProduct_comm, hB, ← mulVec_mulVec,
      dotProduct_mulVec, star_mulVec]
  rw [h1, dotProduct, Complex.re_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Pi.star_apply, Complex.star_def, Complex.conj_mul']
  norm_cast

private lemma ellvol_ball {g : ℕ} (hg : 0 < g) {r : ℝ} (hr : 0 < r) :
    volume {v : Fin g → ℂ | ∑ k, ‖v k‖ ^ 2 < r ^ 2} =
      ENNReal.ofReal (Real.pi ^ g * r ^ (2 * g) / g.factorial) := by
  haveI : Nonempty (Fin g) := ⟨⟨0, hg⟩⟩
  have hset : {v : Fin g → ℂ | ∑ k, ‖v k‖ ^ 2 < r ^ 2} =
      {x : Fin g → ℂ | (∑ i, ‖x i‖ ^ (2:ℝ)) ^ (1 / (2:ℝ)) < r} := by
    ext v
    simp only [Set.mem_setOf_eq, Real.rpow_two]
    have h0 : 0 ≤ ∑ i, ‖v i‖ ^ 2 := by positivity
    rw [← Real.sqrt_eq_rpow, Real.sqrt_lt' hr]
  rw [hset, Complex.volume_sum_rpow_lt (Fin g) (by norm_num) r]
  have e1 : (2:ℝ) / 2 + 1 = 2 := by norm_num
  have e2 : 2 * (Fintype.card (Fin g) : ℝ) / 2 + 1 = (g : ℝ) + 1 := by
    rw [Fintype.card_fin]; ring
  rw [e1, e2, Real.Gamma_two, Real.Gamma_nat_eq_factorial, Fintype.card_fin, mul_one,
    ← ENNReal.ofReal_pow hr.le, ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  ring

theorem volume_hermitian_ellipsoid : ∀ (g : ℕ) (Hm : Matrix (Fin g) (Fin g) ℂ) (r : ℝ), Hm.PosDef → 0 < r →
    volume {w : Fin g → ℂ | (w ⬝ᵥ Hm.mulVec (star w)).re < r ^ 2} =
      ENNReal.ofReal (Real.pi ^ g * r ^ (2 * g) / (g.factorial * Hm.det.re)) := by
  intro g Hm r hH hr
  obtain ⟨B, hB⟩ := ellvol_factor hH.transpose
  have hdet : Hm.det = (Complex.normSq B.det : ℂ) := by
    rw [← det_transpose, hB, det_mul, det_conjTranspose, Complex.normSq_eq_conj_mul_self]; rfl
  have hd : 0 < Complex.normSq B.det := by
    have := hH.det_pos; rwa [hdet, Complex.zero_lt_real] at this
  have hre : Hm.det.re = Complex.normSq B.det := by rw [hdet, Complex.ofReal_re]
  have hset : {w : Fin g → ℂ | (w ⬝ᵥ Hm.mulVec (star w)).re < r ^ 2} =
      ((Matrix.toLin' B).restrictScalars ℝ) ⁻¹' {v : Fin g → ℂ | ∑ k, ‖v k‖ ^ 2 < r ^ 2} := by
    ext w
    simp [ellvol_form Hm B hB w, Matrix.toLin'_apply]
  have hdetL : LinearMap.det ((Matrix.toLin' B).restrictScalars ℝ) = Complex.normSq B.det := by
    rw [LinearMap.det_restrictScalars, LinearMap.det_toLin', Algebra.norm_complex_apply]
  rw [hset, Measure.addHaar_preimage_linearMap _ (by rw [hdetL]; exact hd.ne'), hdetL, hre]
  rcases Nat.eq_zero_or_pos g with rfl | hg
  · have hu : {v : Fin 0 → ℂ | ∑ k, ‖v k‖ ^ 2 < r ^ 2} = Set.univ := by
      ext v; simp [hr.ne', sq_pos_of_pos hr]
    have h1 : Complex.normSq B.det = 1 := by simp
    rw [hu, h1, ← Set.pi_univ Set.univ, volume_pi_pi]
    simp
  · rw [ellvol_ball hg hr, ← ENNReal.ofReal_mul (abs_nonneg _)]
    congr 1
    rw [abs_of_pos (inv_pos.mpr hd)]
    field_simp

end GlobalTheory
