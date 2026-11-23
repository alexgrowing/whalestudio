import Mathlib

open MeasureTheory

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3.BallC

theorem volume_normSq_le_one (M : ℕ) :
    volume {x : Fin M → ℂ | ∑ i, Complex.normSq (x i) ≤ 1} =
      ENNReal.ofReal (Real.pi ^ M / (M.factorial : ℝ)) := by
  rcases Nat.eq_zero_or_pos M with rfl | hM
  · have e : {x : Fin 0 → ℂ | ∑ i, Complex.normSq (x i) ≤ 1} = Set.univ := by
      ext x; simp
    rw [e, MeasureTheory.volume_pi, MeasureTheory.Measure.pi_univ]
    simp
  · haveI : Nonempty (Fin M) := ⟨⟨0, hM⟩⟩
    have h := Complex.volume_sum_rpow_le (Fin M) (p := 2) one_le_two 1
    have hset : {x : Fin M → ℂ | ∑ i, Complex.normSq (x i) ≤ 1} =
        {x : Fin M → ℂ | (∑ i, ‖x i‖ ^ (2 : ℝ)) ^ (1 / (2 : ℝ)) ≤ 1} := by
      ext x
      simp only [Set.mem_setOf_eq]
      rw [← Real.sqrt_eq_rpow, Real.sqrt_le_one]
      simp only [Real.rpow_two, Complex.normSq_eq_norm_sq]
    rw [hset, h, Fintype.card_fin, ENNReal.ofReal_one, one_pow, one_mul]
    congr 1
    have e1 : (2 : ℝ) / 2 + 1 = 2 := by norm_num
    have e2 : 2 * (M : ℝ) / 2 + 1 = (M : ℝ) + 1 := by ring
    rw [e1, e2, Real.Gamma_two, mul_one, Real.Gamma_nat_eq_factorial]

def ell {M : ℕ} (a : Fin M → ℝ) : Set (Fin M → ℂ) := {z | ∑ i, a i * Complex.normSq (z i) ≤ 1}

variable {M : ℕ} (a : Fin M → ℝ)

theorem mem_ell {z : Fin M → ℂ} : z ∈ ell a ↔ ∑ i, a i * Complex.normSq (z i) ≤ 1 := Iff.rfl

theorem isClosed_ell : IsClosed (ell a) := by
  unfold ell
  exact isClosed_le (continuous_finset_sum _ fun i _ =>
    continuous_const.mul (Complex.continuous_normSq.comp (continuous_apply i))) continuous_const

variable {a}

theorem volume_ell (ha : ∀ i, 0 < a i) :
    volume (ell a) = ENNReal.ofReal (Real.pi ^ M / (M.factorial : ℝ) / ∏ i, a i) := by
  let g : Fin M → (ℂ →ₗ[ℝ] ℂ) := fun i => Real.sqrt (a i) • LinearMap.id
  let f : (Fin M → ℂ) →ₗ[ℝ] (Fin M → ℂ) := LinearMap.pi fun i => (g i) ∘ₗ LinearMap.proj i
  have hf : ∀ z i, f z i = (Real.sqrt (a i) : ℂ) * z i := by
    intro z i
    simp [f, g, Complex.real_smul]
  have hdet : LinearMap.det f = ∏ i, a i := by
    rw [LinearMap.det_pi]
    refine Finset.prod_congr rfl fun i _ => ?_
    simp only [g, LinearMap.det_smul, LinearMap.det_id, mul_one, Complex.finrank_real_complex]
    exact Real.sq_sqrt (ha i).le
  have hs : ∀ z, ∑ i, Complex.normSq (f z i) = ∑ i, a i * Complex.normSq (z i) := by
    intro z
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hf, Complex.normSq_mul, Complex.normSq_ofReal, Real.mul_self_sqrt (ha i).le]
  have hpre : ell a = f ⁻¹' {x | ∑ i, Complex.normSq (x i) ≤ 1} := by
    ext z
    simp only [ell, Set.mem_setOf_eq, Set.mem_preimage, hs]
  have hprod : 0 < ∏ i, a i := Finset.prod_pos fun i _ => ha i
  rw [hpre, MeasureTheory.Measure.addHaar_preimage_linearMap _ (by rw [hdet]; exact hprod.ne'),
    volume_normSq_le_one, hdet, ← ENNReal.ofReal_mul (abs_nonneg _)]
  congr 1
  rw [abs_of_pos (inv_pos.mpr hprod)]
  ring

theorem convex_ell (ha : ∀ i, 0 < a i) : Convex ℝ (ell a) := by
  intro x hx y hy s t hs ht hst
  simp only [ell, Set.mem_setOf_eq] at hx hy ⊢
  have key : ∀ i, a i * Complex.normSq ((s • x + t • y) i) ≤
      s * (a i * Complex.normSq (x i)) + t * (a i * Complex.normSq (y i)) := by
    intro i
    have h1 : Complex.normSq ((s • x + t • y) i) ≤
        s * Complex.normSq (x i) + t * Complex.normSq (y i) := by
      simp only [Pi.add_apply, Pi.smul_apply, Complex.normSq_apply, Complex.add_re, Complex.add_im,
        Complex.real_smul, Complex.re_ofReal_mul, Complex.im_ofReal_mul]
      have ht' : t = 1 - s := by linarith
      subst ht'
      nlinarith [mul_nonneg (mul_nonneg hs ht) (sq_nonneg ((x i).re - (y i).re)),
        mul_nonneg (mul_nonneg hs ht) (sq_nonneg ((x i).im - (y i).im))]
    calc a i * Complex.normSq ((s • x + t • y) i)
        ≤ a i * (s * Complex.normSq (x i) + t * Complex.normSq (y i)) :=
          mul_le_mul_of_nonneg_left h1 (ha i).le
      _ = s * (a i * Complex.normSq (x i)) + t * (a i * Complex.normSq (y i)) := by ring
  calc ∑ i, a i * Complex.normSq ((s • x + t • y) i)
      ≤ ∑ i, (s * (a i * Complex.normSq (x i)) + t * (a i * Complex.normSq (y i))) :=
        Finset.sum_le_sum fun i _ => key i
    _ = s * ∑ i, a i * Complex.normSq (x i) + t * ∑ i, a i * Complex.normSq (y i) := by
        rw [Finset.sum_add_distrib, Finset.mul_sum, Finset.mul_sum]
    _ ≤ s * 1 + t * 1 := by gcongr
    _ = 1 := by rw [mul_one, mul_one, hst]

theorem isBounded_ell (ha : ∀ i, 0 < a i) : Bornology.IsBounded (ell a) := by
  rw [Metric.isBounded_iff_subset_closedBall 0]
  refine ⟨∑ i, (1 + (a i)⁻¹), fun z hz => ?_⟩
  rw [mem_closedBall_zero_iff]
  simp only [ell, Set.mem_setOf_eq] at hz
  have hnn : ∀ j, 0 ≤ 1 + (a j)⁻¹ := fun j => add_nonneg zero_le_one (inv_nonneg.mpr (ha j).le)
  refine (pi_norm_le_iff_of_nonneg (Finset.sum_nonneg fun i _ => hnn i)).mpr fun i => ?_
  have hi : a i * Complex.normSq (z i) ≤ 1 :=
    le_trans (Finset.single_le_sum (f := fun j => a j * Complex.normSq (z j))
      (fun j _ => mul_nonneg (ha j).le (Complex.normSq_nonneg _)) (Finset.mem_univ i)) hz
  have h2 : Complex.normSq (z i) ≤ (a i)⁻¹ := by
    rw [← one_div, le_div_iff₀ (ha i), mul_comm]
    exact hi
  rw [Complex.normSq_eq_norm_sq] at h2
  have h3 : ‖z i‖ ≤ 1 + (a i)⁻¹ := by nlinarith [sq_nonneg (‖z i‖ - 1)]
  exact h3.trans (Finset.single_le_sum (f := fun j => 1 + (a j)⁻¹) (fun j _ => hnn j)
    (Finset.mem_univ i))

end Formalism.HermitianLattices.Ext.L3.BallC
