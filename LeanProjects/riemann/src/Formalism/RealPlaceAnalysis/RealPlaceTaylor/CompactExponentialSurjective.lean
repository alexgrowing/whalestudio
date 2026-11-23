import Formalism.RealPlaceAnalysis.SmoothOnGVIff
import Formalism.RealPlaceAnalysis.RealPlaceTaylor.IndefiniteUnitaryPreservesForm

open Matrix
open scoped Matrix.Norms.L2Operator

noncomputable section
namespace Formalism.REAL

lemma norm_log_sq_le_unit_circle (z : ℂ) (hz : ‖z‖ = 1) : ‖Complex.log z‖ ^ 2 ≤ 3 * ‖z - 1‖ ^ 2 := by
  have hz0 : z ≠ 0 := by
    rintro rfl
    simp at hz
  set θ := Complex.arg z with hθ
  have hre : z.re = Real.cos θ := by rw [Complex.cos_arg hz0, hz, div_one]
  have him : z.im = Real.sin θ := by rw [Complex.sin_arg, hz, div_one]
  have hlog : ‖Complex.log z‖ ^ 2 = θ ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply, Complex.log_re, Complex.log_im, hz, Real.log_one]
    ring
  have hc : Real.cos θ = 1 - 2 * Real.sin (θ / 2) ^ 2 := by
    have h1 := Real.cos_sq_add_sin_sq (θ / 2)
    have h2 := Real.cos_two_mul (θ / 2)
    rw [show 2 * (θ / 2) = θ by ring] at h2
    linarith
  have hsub : ‖z - 1‖ ^ 2 = 4 * Real.sin (θ / 2) ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.one_re,
      Complex.one_im, hre, him]
    linear_combination Real.cos_sq_add_sin_sq θ - 2 * hc
  have key : ∀ y : ℝ, 0 ≤ y → y ≤ Real.pi / 2 → 4 * y ^ 2 ≤ 12 * Real.sin y ^ 2 := by
    intro y hy0 hy1
    have hs := Real.mul_le_sin hy0 hy1
    have hpi0 := Real.pi_pos
    have hpi : Real.pi ^ 2 ≤ 12 := by nlinarith [Real.pi_lt_d2]
    have ha0 : 0 ≤ 2 / Real.pi * y := by positivity
    have h1 : (2 / Real.pi * y) ^ 2 ≤ Real.sin y ^ 2 := pow_le_pow_left₀ ha0 hs 2
    have h2 : 4 * y ^ 2 = Real.pi ^ 2 * (2 / Real.pi * y) ^ 2 := by
      field_simp
      ring
    rw [h2]
    nlinarith [sq_nonneg (2 / Real.pi * y)]
  have hb : |θ| ≤ Real.pi := abs_le.2 ⟨(Complex.neg_pi_lt_arg z).le, Complex.arg_le_pi z⟩
  rw [hlog, hsub]
  rcases le_or_gt 0 θ with h | h
  · have := key (θ / 2) (by linarith) (by rw [abs_of_nonneg h] at hb; linarith)
    nlinarith
  · have := key (-(θ / 2)) (by linarith) (by rw [abs_of_neg h] at hb; linarith)
    rw [Real.sin_neg, neg_sq, neg_sq] at this
    nlinarith

lemma frobenius_eq_trace {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) :
    ((hs A : ℝ) : ℂ) = (star A * A).trace := by
  simp only [hs, Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.star_apply]
  push_cast
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [Complex.star_def, Complex.conj_mul']

lemma frobenius_nonneg_matrix {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ) : 0 ≤ hs A := by
  unfold hs
  positivity

lemma compact_exists_log_bounded {n : ℕ} (ε : Fin n → Bool) (k : Matrix (Fin n) (Fin n) ℂ) (hk : k ∈ Kset ε) :
    ∃ Y : Matrix (Fin n) (Fin n) ℂ, inK ε Y ∧ NormedSpace.exp Y = k ∧ hs Y ≤ 3 * hs (k - 1) := by
  obtain ⟨hu, hJ⟩ := hk
  have hN : IsStarNormal k := isStarNormal_of_mem_unitary hu
  have hcont : ∀ f : ℂ → ℂ, ContinuousOn f (spectrum ℂ k) :=
    fun f => (Matrix.finite_spectrum k).continuousOn f
  have hcirc : ∀ z ∈ spectrum ℂ k, ‖z‖ = 1 := fun z hz => spectrum.norm_eq_one_of_unitary hu hz
  have hJs : star (Jm ε) = Jm ε := by rw [Matrix.star_eq_conjTranspose, Jm_conjTranspose]
  have hstarJ : star k * Jm ε = Jm ε * star k := by
    have := congrArg star hJ
    simp only [star_mul, hJs] at this
    exact this.symm
  set Y := cfc Complex.log k with hY
  have hcomm : Commute Y (Jm ε) := Commute.cfc hJ hstarJ Complex.log
  have hstarY : star Y = -Y := by
    rw [hY, ← cfc_star, ← cfc_neg Complex.log k]
    refine cfc_congr fun z hz => ?_
    have h1 := hcirc z hz
    apply Complex.ext <;> simp [Complex.log_re, Complex.log_im, h1]
  refine ⟨Y, ⟨?_, hcomm.eq⟩, ?_, ?_⟩
  · show Yᴴ * Jm ε + Jm ε * Y = 0
    rw [← Matrix.star_eq_conjTranspose, hstarY, neg_mul, hcomm.eq]
    exact neg_add_cancel _
  · rw [← CFC.complex_exp_eq_normedSpace_exp, hY,
      ← cfc_comp Complex.exp Complex.log k (hg := Complex.continuous_exp.continuousOn) (hf := hcont _)]
    rw [cfc_congr (g := id) (fun z hz => by
      have h1 := hcirc z hz
      have h0 : z ≠ 0 := by
        rintro rfl
        simp at h1
      simp [Complex.exp_log h0])]
    exact cfc_id ℂ k
  · (have hF : cfc (fun z => 3 * (star (z - 1) * (z - 1)) - star (Complex.log z) * Complex.log z) k =
        (3 : ℂ) • (star (k - 1) * (k - 1)) - star Y * Y := by
       rw [cfc_sub (fun z => 3 * (star (z - 1) * (z - 1))) (fun z => star (Complex.log z) * Complex.log z) k
         (hcont _) (hcont _)]
       rw [cfc_const_mul 3 (fun z => star (z - 1) * (z - 1)) k (hcont _)]
       rw [cfc_mul (fun z => star (z - 1)) (fun z => z - 1) k (hcont _) (hcont _)]
       rw [cfc_mul (fun z => star (Complex.log z)) Complex.log k (hcont _) (hcont _)]
       rw [cfc_star (fun z => z - 1) k, cfc_star Complex.log k]
       rw [cfc_sub (fun z => z) (fun _ => 1) k (hcont _) (hcont _), cfc_id' ℂ k, cfc_const_one ℂ k]
     set G := cfc (fun z => ((Real.sqrt (3 * ‖z - 1‖ ^ 2 - ‖Complex.log z‖ ^ 2) : ℝ) : ℂ)) k with hG
     have hFG : cfc (fun z => 3 * (star (z - 1) * (z - 1)) - star (Complex.log z) * Complex.log z) k =
         star G * G := by
       rw [hG, ← cfc_star, ← cfc_mul _ _ k (hcont _) (hcont _)]
       refine cfc_congr fun z hz => ?_
       have hsc := norm_log_sq_le_unit_circle z (hcirc z hz)
       have hnn : 0 ≤ 3 * ‖z - 1‖ ^ 2 - ‖Complex.log z‖ ^ 2 := by linarith
       simp only [Complex.star_def, Complex.conj_ofReal]
       rw [Complex.conj_mul', Complex.conj_mul', ← Complex.ofReal_mul, Real.mul_self_sqrt hnn]
       push_cast
       ring
     have htr := congrArg Matrix.trace (hF.symm.trans hFG)
     rw [Matrix.trace_sub, Matrix.trace_smul, ← frobenius_eq_trace, ← frobenius_eq_trace, ← frobenius_eq_trace,
       smul_eq_mul] at htr
     have h4 : (3 : ℂ) * (hs (k - 1) : ℂ) - (hs Y : ℂ) = ((3 * hs (k - 1) - hs Y : ℝ) : ℂ) := by push_cast; ring
     rw [h4] at htr
     have h5 := Complex.ofReal_injective htr
     have h6 := frobenius_nonneg_matrix G
     linarith)

theorem compact_exponential_surjective : KExp := fun _ ε k hk => compact_exists_log_bounded ε k hk

theorem genExp_of (h : KExp) : GenExp := by
  intro n ε g hg
  obtain ⟨k, X, hk, hX, rfl⟩ := (polar_decomposition_holds n ε).1 g hg
  obtain ⟨Z, hZ, hZk, -⟩ := h n ε k hk
  exact ⟨Z, X, hZ, hX, by rw [hZk]⟩

end Formalism.REAL
